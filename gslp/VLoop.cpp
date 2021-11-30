#include "VLoop.h"
#include "ControlDependence.h"
#include "DependenceAnalysis.h"
#include "VectorPackContext.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"

using namespace llvm;

static void setSubtract(BitVector &Src, BitVector ToRemove) {
  ToRemove.flip();
  Src &= ToRemove;
}

VLoop::VLoop(LoopInfo &LI, VectorPackContext *VPCtx,
             GlobalDependenceAnalysis &DA, ControlDependenceAnalysis &CDA,
             VLoopInfo &VLI)
    : IsTopLevel(true), Parent(nullptr), LoopCond(nullptr), L(nullptr) {
  for (auto *L : LI.getTopLevelLoops()) {
    auto *SubVL = new VLoop(LI, L, VPCtx, DA, CDA, VLI);
    SubVL->Parent = this;
    SubLoops.emplace_back(SubVL);
  }

  for (auto &BB : *VPCtx->getFunction())
    if (!LI.getLoopFor(&BB)) {
      auto *C = CDA.getConditionForBlock(&BB);
      for (auto &I : BB) {
        TopLevelInsts.push_back(&I);
        InstConds[&I] = C;
      }
    }
}

VLoop::VLoop(LoopInfo &LI, Loop *L, VectorPackContext *VPCtx,
             GlobalDependenceAnalysis &DA, ControlDependenceAnalysis &CDA,
             VLoopInfo &VLI)
    : IsTopLevel(false), Depended(VPCtx->getNumValues()),
      LoopCond(CDA.getConditionForBlock(L->getLoopPreheader())),
      Insts(VPCtx->getNumValues()), L(L), Parent(nullptr) {
  VLI.setVLoop(L, this);
  // assert(L->isRotatedForm());

  auto *Preheader = L->getLoopPreheader();
  auto *Header = L->getHeader();
  auto *Latch = L->getLoopLatch();

  SmallVector<BasicBlock *> Exits;
  L->getUniqueExitBlocks(Exits);
  // Assume LCSSA so the live-outs are guarded by PHIs
  for (auto *Exit : Exits) {
    for (auto &PN : Exit->phis()) {
      for (Value *V : PN.incoming_values()) {
        if (auto *I = dyn_cast<Instruction>(V))
          LiveOuts.insert(I);
      }
    }
  }

  // Figure out the condition for taking the backedge (vs exiting the loop)
  auto *LoopBr = cast<BranchInst>(Latch->getTerminator());
  auto *LatchCond = CDA.getConditionForBlock(Latch);
  // Back edge taken === reaches latch && back edge taken
  if (LoopBr->isConditional())
    BackEdgeCond = CDA.getAnd(LatchCond, LoopBr->getCondition(),
                              LoopBr->getSuccessor(0) == L->getHeader());
  else
    BackEdgeCond = LatchCond;

  // Build the sub-loops
  for (auto *SubL : *L) {
    auto *SubVL = new VLoop(LI, SubL, VPCtx, DA, CDA, VLI);
    SubLoops.emplace_back(SubVL);
    SubVL->Parent = this;
    Depended |= SubVL->getDepended();
    Insts |= SubVL->Insts;
  }

  // Figure out the eta nodes
  for (PHINode &PN : Header->phis()) {
    assert(PN.getNumIncomingValues() == 2);
    Mus.try_emplace(&PN, PN.getIncomingValueForBlock(Preheader),
                    PN.getIncomingValueForBlock(Latch));
  }

  // Process the top-level instructions
  for (auto *BB : L->blocks()) {
    if (LI.getLoopFor(BB) != L)
      continue;
    auto *C = CDA.getConditionForBlock(BB);
    for (auto &I : *BB) {
      Depended |= DA.getDepended(&I);
      TopLevelInsts.push_back(&I);
      InstConds[&I] = C;
      Insts.set(VPCtx->getScalarId(&I));
    }
  }

  setSubtract(Depended, Insts);
}

llvm::Optional<MuNode> VLoop::getMu(PHINode *PN) const {
  auto It = Mus.find(PN);
  if (It != Mus.end())
    return It->second;
  return None;
}

bool haveIdenticalTripCounts(const Loop *L1, const Loop *L2,
                             ScalarEvolution &SE) {
  if (L1 == L2)
    return true;

  auto *TripCount1 = SE.getBackedgeTakenCount(L1);
  auto *TripCount2 = SE.getBackedgeTakenCount(L2);
  if (!isa<SCEVCouldNotCompute>(TripCount1) &&
      !isa<SCEVCouldNotCompute>(TripCount2) && TripCount1 == TripCount2)
    return true;

  auto *BB1 = L1->getExitingBlock();
  if (!BB1)
    return false;

  auto *BB2 = L2->getExitingBlock();
  if (!BB2)
    return false;

  using namespace PatternMatch;

  Value *LHS1, *RHS1;
  ICmpInst::Predicate Pred1;
  if (!match(BB1->getTerminator(),
             m_Br(m_ICmp(Pred1, m_Value(LHS1), m_Value(RHS1)), m_BasicBlock(),
                  m_BasicBlock())))
    return false;

  Value *LHS2, *RHS2;
  ICmpInst::Predicate Pred2;
  if (!match(BB2->getTerminator(),
             m_Br(m_ICmp(Pred2, m_Value(LHS2), m_Value(RHS2)), m_BasicBlock(),
                  m_BasicBlock())))
    return false;

  if (Pred1 != Pred2)
    return false;

  if (RHS1 != RHS2)
    return false;

  auto *Expr1 = dyn_cast<SCEVAddRecExpr>(SE.getSCEV(LHS1));
  if (!Expr1 || !Expr1->isAffine() || Expr1->getLoop() != L1)
    return false;

  auto *Expr2 = dyn_cast<SCEVAddRecExpr>(SE.getSCEV(LHS2));
  if (!Expr2 || !Expr1->isAffine() || Expr2->getLoop() != L2)
    return false;

  return Expr1->getOperand(0) == Expr2->getOperand(0) &&
         Expr1->getOperand(1) == Expr2->getOperand(1);
}

bool VLoop::isSafeToFuse(VLoop *VL1, VLoop *VL2, ScalarEvolution &SE) {
  if (VL1 == VL2)
    return true;

  // The loops should be control-equivalent
  if (VL1->LoopCond != VL2->LoopCond)
    return false;

  // Loop level mismatch
  if (!VL1 || !VL2)
    return false;

  // Make sure the loops are independent
  if (VL1->Insts.anyCommon(VL2->Depended) ||
      VL2->Insts.anyCommon(VL1->Depended))
    return false;

  if (!VL1->haveIdenticalTripCounts(VL2, SE))
    return false;

  return isSafeToFuse(VL1->Parent, VL2->Parent, SE);
}

// FIXME : move this to VLoopInfo and check all loops that we are already
// coiterating with VL1 or VL2
bool VLoop::isSafeToCoIterate(const VLoop *VL1, const VLoop *VL2) {
  if (VL1 == VL2)
    return true;

  // Loop level mismatch
  if (!VL1 || !VL2)
    return false;

  // Make sure the loops are independent
  if (VL1->Insts.anyCommon(VL2->Depended) ||
      VL2->Insts.anyCommon(VL1->Depended))
    return false;

  return isSafeToCoIterate(VL1->Parent, VL2->Parent);
}

bool VLoop::haveIdenticalTripCounts(VLoop *VL2, llvm::ScalarEvolution &SE) {
  return ::haveIdenticalTripCounts(L, VL2->L, SE);
}

void VLoopInfo::fuse(VLoop *VL1, VLoop *VL2) {
  assert(VL1 != VL2 && "can't fuse the same loop with itself");
  auto *Parent = VL1->Parent;
  if (Parent != VL2->Parent)
    fuse(VL1->Parent, VL2->Parent);
  setVLoop(VL2->L, VL1);
  VL1->Insts |= VL2->Insts;
  VL1->Depended |= VL2->Depended;
  VL1->TopLevelInsts.append(VL2->TopLevelInsts);
  for (auto KV : VL2->InstConds)
    VL1->InstConds.insert(KV);
  for (auto KV : VL2->Mus)
    VL1->Mus.insert(KV);
  for (auto &SubVL : VL2->SubLoops)
    VL1->SubLoops.emplace_back(SubVL.release());
  VL1->Allocas.append(VL2->Allocas);

  DeletedLoops.insert(VL2);
  VL2->Parent = Parent;

  assert(Parent);
  auto It = llvm::find_if(Parent->SubLoops, [VL2](std::unique_ptr<VLoop> &VL) {
    return VL.get() == VL2;
  });
  assert(It != Parent->SubLoops.end());
  assert(It->get() == VL2);
  Parent->SubLoops.erase(It);
}

void VLoopInfo::coiterate(VLoop *VL1, VLoop *VL2) {
  CoIteratingLoops.unionSets(VL1, VL2);
}

bool VLoopInfo::isCoIterating(VLoop *VL) const {
  auto It = CoIteratingLoops.findValue(VL);
  return std::next(CoIteratingLoops.member_begin(It)) !=
         CoIteratingLoops.member_end();
}

void VLoopInfo::doCoiteration(LLVMContext &Ctx,
                              ControlDependenceAnalysis &CDA) {
  DenseSet<VLoop *> Visited;
  std::function<void(VLoop *)> Visit = [&](VLoop *VL) {
    if (!Visited.insert(VL).second)
      return;

    // Coiterate the parents if necessary
    if (isCoIterating(VL->Parent))
      Visit(VL->Parent);

    auto *ParentVL = VL->Parent;

    auto Members = getCoIteratingLoops(VL);
    // 1) Transform the loops to
    //    * add active guard
    //    * guard the live-outs
    auto *Int1Ty = Type::getInt1Ty(Ctx);
    auto *True = ConstantInt::getTrue(Ctx);
    auto *False = ConstantInt::getFalse(Ctx);
    SmallVector<const ControlCondition *, 8> LoopConds, BackEdgeConds;
    for (auto *CoVL : Members) {
      auto *ActivePhi = PHINode::Create(Int1Ty, 2);
      auto *Active = CDA.getAnd(nullptr, ActivePhi, true);
      auto *ShouldContinue = CDA.concat(Active, CoVL->BackEdgeCond);

      // Guard all loops and instructions nested inside CoVL
      for (auto &KV : CoVL->InstConds)
        KV.second = CDA.concat(Active, KV.second);
      for (std::unique_ptr<VLoop> &SubVL : CoVL->SubLoops)
        SubVL->LoopCond = CDA.concat(Active, SubVL->LoopCond);

      // Guard the live-outs
      SmallVector<Instruction *> InstsToGuard;
      for (auto *I : CoVL->TopLevelInsts)
        if (!I->getType()->isVoidTy())
          InstsToGuard.push_back(I);
      for (auto *I : InstsToGuard) {
        auto *Ty = I->getType();
        auto *Phi = PHINode::Create(Ty, 2);
        auto *Guarded =
            CoVL->createOneHotPhi(CoVL->InstConds.lookup(I), I, Phi);
        CoVL->Mus.try_emplace(Phi, UndefValue::get(Ty), Guarded);
        CoVL->GuardedLiveOuts[I] = Guarded;
      }

      ParentVL->addInstruction(ActivePhi, nullptr);
      CoVL->Mus.try_emplace(
          ActivePhi,
          ParentVL->createOneHotPhi(CoVL->LoopCond, True, False) /*init*/,
          ParentVL->createOneHotPhi(ShouldContinue, True, False) /*recur*/);

      LoopConds.push_back(CoVL->LoopCond);
      BackEdgeConds.push_back(ShouldContinue);
    }

    // 2) Fuse them
    VLoop *Leader = *Members.begin();
    for (VLoop *CoVL : drop_begin(Members))
      fuse(Leader, CoVL);

    Leader->LoopCond = getGreatestCommonCondition(LoopConds);
    Leader->BackEdgeCond = CDA.getOr(BackEdgeConds);
  };
}

Instruction *VLoop::createOneHotPhi(const ControlCondition *C, Value *IfTrue, Value *IfFalse) {
  auto *PN = PHINode::Create(IfTrue->getType(), 2);
  OneHotPhis.try_emplace(PN, C, IfTrue, IfFalse);
  addInstruction(PN, nullptr);
  return PN;
}

VLoop *VLoopInfo::getVLoop(Loop *L) const { return LoopToVLoopMap.lookup(L); }

void VLoopInfo::setVLoop(Loop *L, VLoop *VL) {
  LoopToVLoopMap[L] = VL;
  CoIteratingLoops.insert(VL);
}
