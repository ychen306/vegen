#include "VLoop.h"
#include "ControlDependence.h"
#include "DependenceAnalysis.h"
#include "VectorPackContext.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"

using namespace llvm;

static void setSubtract(BitVector &Src, BitVector ToRemove) {
  ToRemove.flip();
  Src &= ToRemove;
}

static void
getIncomingPhiConditions(SmallVectorImpl<const ControlCondition *> &Conds,
                         PHINode *PN, ControlDependenceAnalysis &CDA) {
  for (auto *SrcBB : PN->blocks())
    Conds.push_back(CDA.getConditionForEdge(SrcBB, PN->getParent()));
}

VLoop::VLoop(LoopInfo &LI, DominatorTree &DT, VectorPackContext *VPCtx,
             GlobalDependenceAnalysis &DA, ControlDependenceAnalysis &CDA,
             VLoopInfo &VLI)
    : IsTopLevel(true), Parent(nullptr), LoopCond(nullptr), L(nullptr),
      VPCtx(VPCtx), DA(DA), VLI(VLI) {
  for (auto *L : LI.getTopLevelLoops()) {
    auto *SubVL = new VLoop(LI, L, VPCtx, DA, CDA, VLI);
    SubVL->Parent = this;
    SubLoops.emplace_back(SubVL);
  }

  for (auto &BB : *VPCtx->getFunction()) {
    // Ignore dead basic blocks
    if (!DT.isReachableFromEntry(&BB))
      continue;

    if (!LI.getLoopFor(&BB)) {
      auto *C = CDA.getConditionForBlock(&BB);
      for (auto &I : BB) {
        TopLevelInsts.push_back(&I);
        InstConds[&I] = C;
        if (auto *PN = dyn_cast<PHINode>(&I))
          getIncomingPhiConditions(GatedPhis[PN], PN, CDA);
        VLI.mapInstToLoop(&I, this);
      }
    }
  }
}

VLoop::VLoop(LoopInfo &LI, Loop *L, VectorPackContext *VPCtx,
             GlobalDependenceAnalysis &DA, ControlDependenceAnalysis &CDA,
             VLoopInfo &VLI)
    : IsTopLevel(false), Depended(VPCtx->getNumValues()),
      LoopCond(CDA.getConditionForBlock(L->getLoopPreheader())),
      Insts(VPCtx->getNumValues()), L(L), Parent(nullptr), VPCtx(VPCtx), DA(DA),
      VLI(VLI) {
  VLI.setVLoop(L, this);
  // assert(L->isRotatedForm());

  auto *Preheader = L->getLoopPreheader();
  auto *Header = L->getHeader();
  auto *Latch = L->getLoopLatch();

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

  // Figure out the mu nodes
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
      VLI.mapInstToLoop(&I, this);
      auto *PN = dyn_cast<PHINode>(&I);
      if (PN && !getMu(PN))
        getIncomingPhiConditions(GatedPhis[PN], PN, CDA);
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

llvm::Optional<OneHotPhi> VLoop::getOneHotPhi(PHINode *PN) const {
  auto It = OneHotPhis.find(PN);
  if (It != OneHotPhis.end())
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

bool VLoop::isSafeToFuse(VLoop *VL1, VLoop *VL2, ControlDependenceAnalysis &CDA, ScalarEvolution &SE) {
  if (VL1 == VL2)
    return true;

  // The loops should be control-equivalent
  if (!CDA.isEquivalent(VL1->LoopCond, VL2->LoopCond))
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

  return isSafeToFuse(VL1->Parent, VL2->Parent, CDA, SE);
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

namespace {

template <typename MapTy> void mergeMap(MapTy &Dst, const MapTy &Src) {
  Dst.insert(Src.begin(), Src.end());
}

} // namespace

void VLoopInfo::fuse(VLoop *VL1, VLoop *VL2) {
  assert(VL1 != VL2 && "can't fuse the same loop with itself");
  auto *Parent = VL1->Parent;
  if (Parent != VL2->Parent)
    fuse(VL1->Parent, VL2->Parent);
  setVLoop(VL2->L, VL1);
  VL1->Insts |= VL2->Insts;
  VL1->Depended |= VL2->Depended;
  for (auto *I : VL2->TopLevelInsts)
    mapInstToLoop(I, VL1);
  VL1->TopLevelInsts.append(VL2->TopLevelInsts);
  mergeMap(VL1->InstConds, VL2->InstConds);
  mergeMap(VL1->Mus, VL2->Mus);
  mergeMap(VL1->OneHotPhis, VL2->OneHotPhis);
  mergeMap(VL1->GatedPhis, VL2->GatedPhis);
  mergeMap(VL1->GuardedLiveOuts, VL2->GuardedLiveOuts);
  for (auto &SubVL : VL2->SubLoops)
    VL1->SubLoops.emplace_back(SubVL.release())->Parent = VL1;

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
  if (VL1->Parent) {
    assert(VL2->Parent);
    coiterate(VL1->Parent, VL2->Parent);
  }
  CoIteratingLoops.unionSets(VL1, VL2);
}

bool VLoopInfo::isCoIterating(VLoop *VL) const {
  if (!VL->isLoop())
    return false;
  auto It = CoIteratingLoops.findValue(VL);
  return std::next(CoIteratingLoops.member_begin(It)) !=
         CoIteratingLoops.member_end();
}

bool VLoop::contains(Instruction *I) const {
  return Insts.test(VPCtx->getScalarId(I));
}

bool VLoop::contains(VLoop *VL) const {
  for (auto &SubVL : SubLoops)
    if (SubVL.get() == VL || SubVL->contains(VL))
      return true;
  return true;
}

// Determine whether I has user from out of VL
static bool hasOutsideUser(VLoop *VL, Instruction *I) {
  return any_of(I->users(), [VL](User *U) {
    auto *UI = dyn_cast<Instruction>(U);
    return UI && !VL->contains(UI);
  });
}

void VLoopInfo::doCoiteration(LLVMContext &Ctx, const VectorPackContext &VPCtx,
                              GlobalDependenceAnalysis &DA,
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
    VLoop *Leader = *Members.begin();
    SmallVector<const ControlCondition *, 8> LoopConds, BackEdgeConds;
    for (auto *CoVL : Members) {
      // Insert the active guard for CoVL
      auto *ShouldEnter = ParentVL->createOneHotPhi(CoVL->LoopCond, True, False,
                                                    "loop.active.init");
      auto *ActiveMu = CoVL->createMu(ShouldEnter, "active");
      CoVL->Depended.set(VPCtx.getScalarId(ShouldEnter));
      auto *Active = CDA.getAnd(nullptr, ActiveMu, true);
      auto *ShouldContinue = CDA.concat(Active, CoVL->BackEdgeCond);
      CoVL->setRecursiveMuOperand(
          ActiveMu, CoVL->createOneHotPhi(ShouldContinue, True, False,
                                          "loop.active.recur"));

      LoopConds.push_back(CoVL->LoopCond);
      BackEdgeConds.push_back(ShouldContinue);

      // Guard all loops and instructions nested inside CoVL
      for (auto &KV : CoVL->InstConds)
        KV.second = CDA.concat(Active, KV.second);
      for (std::unique_ptr<VLoop> &SubVL : CoVL->SubLoops)
        SubVL->LoopCond = CDA.concat(Active, SubVL->LoopCond);

      // Also fix the gated phi conditions
      for (auto &KV : CoVL->GatedPhis)
        for (auto &C : KV.second)
          C = CDA.concat(Active, C);

      // Guard the live-outs
      SmallVector<Instruction *> InstsToGuard;
      for (auto *I : CoVL->TopLevelInsts)
        if (!I->getType()->isVoidTy() && I != ActiveMu)
          InstsToGuard.push_back(I);
      for (auto *I : InstsToGuard) {
        if (I->getType() != Int1Ty && !hasOutsideUser(CoVL, I))
          continue;
        auto *Ty = I->getType();
        auto *Mu =
            CoVL->createMu(UndefValue::get(Ty), I->getName() + ".loop.out");
        auto *Guarded = CoVL->createOneHotPhi(CoVL->InstConds.lookup(I), I, Mu,
                                              Mu->getName() + ".next");
        CoVL->setRecursiveMuOperand(Mu, Guarded);
        CoVL->GuardedLiveOuts.try_emplace(I, Guarded);
      }

      // For values coming out a sub loop, we take its value only when the loop
      // executes
      for (auto &SubVL : CoVL->getSubLoops()) {
        auto *SubLoopCond = SubVL->LoopCond;
        for (auto *V : VPCtx.iter_values(SubVL->Insts)) {
          auto *I = cast<Instruction>(V);
          if (I->getType()->isVoidTy())
            continue;
          if (I->getType() != Int1Ty && !hasOutsideUser(CoVL, I))
            continue;
          auto *Ty = I->getType();
          auto *Mu = CoVL->createMu(UndefValue::get(Ty),
                                    I->getName() + ".sub_loop.out");
          auto *Guarded = CoVL->createOneHotPhi(SubLoopCond, I, Mu,
                                                Mu->getName() + ".next");
          CoVL->setRecursiveMuOperand(Mu, Guarded);
          CoVL->GuardedLiveOuts.try_emplace(I, Guarded);
        }
      }
    }

    // 2) Fuse them
    assert(all_of(Members, [Leader](VLoop *CoVL) {
      return CoVL->Parent == Leader->Parent;
    }));
    for (VLoop *CoVL : drop_begin(Members))
      fuse(Leader, CoVL);

    SmallPtrSet<const ControlCondition *, 8> Seen;
    decltype(LoopConds) UniqueLoopConds;
    for (auto *C : LoopConds)
      if (Seen.insert(C).second)
        UniqueLoopConds.push_back(C);

    Leader->LoopCond = CDA.getOr(UniqueLoopConds);
    Leader->BackEdgeCond = CDA.getOr(BackEdgeConds);
  };

  for (auto It = CoIteratingLoops.begin(), E = CoIteratingLoops.end(); It != E;
       It++) {
    auto *VL = *CoIteratingLoops.findLeader(It);
    if (isCoIterating(VL))
      Visit(VL);
  }
}

PHINode *VLoop::createMu(Value *Init, const Twine &Name) {
  auto *PN = PHINode::Create(Init->getType(), 2, Name);
  PN->setNumHungOffUseOperands(1);
  PN->setIncomingValue(0, Init);
  Mus.try_emplace(PN, Init, nullptr);
  addInstruction(PN, nullptr);
  return PN;
}

void VLoop::setRecursiveMuOperand(PHINode *PN, Value *V) {
  assert(Mus.count(PN));
  Mus.find(PN)->second.Iter = V;
  assert(PN->getNumOperands() == 1);
  PN->setNumHungOffUseOperands(2);
  PN->setIncomingValue(1, V);
}

Instruction *VLoop::createOneHotPhi(const ControlCondition *C, Value *IfTrue,
                                    Value *IfFalse, const Twine &Name) {
  auto *PN = PHINode::Create(IfTrue->getType(), 2, Name);
  PN->setNumHungOffUseOperands(2);
  PN->setIncomingValue(0, IfTrue);
  PN->setIncomingValue(1, IfFalse);
  OneHotPhis.try_emplace(PN, C, IfTrue, IfFalse);
  addInstruction(PN, nullptr);
  return PN;
}

void VLoop::addInstruction(Instruction *I, const ControlCondition *C) {
  TopLevelInsts.push_back(I);
  InstConds.insert({I, C});
  VPCtx->addInstruction(I);
  DA.addInstruction(I);
  VLI.mapInstToLoop(I, this);
}

VLoop *VLoopInfo::getVLoop(Loop *L) const { return LoopToVLoopMap.lookup(L); }

void VLoopInfo::setVLoop(Loop *L, VLoop *VL) {
  LoopToVLoopMap[L] = VL;
  CoIteratingLoops.insert(VL);
}

VLoop *VLoop::isLiveOutOfSubLoop(Instruction *I) const {
  for (auto &SubLoop : SubLoops)
    if (VLI.getLoopForInst(I) == SubLoop.get())
      return SubLoop.get();
  return nullptr;
}
