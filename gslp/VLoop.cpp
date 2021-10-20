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
             LoopToVLoopMapTy &LoopToVLoopMap)
    : IsTopLevel(true), Parent(nullptr), LoopCond(nullptr), L(nullptr) {
  for (auto *L : LI.getTopLevelLoops()) {
    auto *SubVL = new VLoop(LI, L, VPCtx, DA, CDA, LoopToVLoopMap);
    SubVL->Parent = this;
    SubLoops.emplace_back(SubVL);
  }

  for (auto &BB : *VPCtx->getFunction())
    if (!LI.getLoopFor(&BB)) {
      for (auto &I : BB)
        TopLevelInsts.push_back(&I);
    }
}

VLoop::VLoop(LoopInfo &LI, Loop *L, VectorPackContext *VPCtx,
             GlobalDependenceAnalysis &DA, ControlDependenceAnalysis &CDA,
             LoopToVLoopMapTy &LoopToVLoopMap)
    : IsTopLevel(false), Depended(VPCtx->getNumValues()),
      LoopCond(CDA.getConditionForBlock(L->getLoopPreheader())),
      Insts(VPCtx->getNumValues()), L(L), Parent(nullptr) {
  LoopToVLoopMap[L] = this;
  assert(L->isRotatedForm());

  auto *Preheader = L->getLoopPreheader();
  auto *Header = L->getHeader();
  auto *Latch = L->getLoopLatch();

  auto *LoopBr = cast<BranchInst>(Latch->getTerminator());
  ContCond = LoopBr->getCondition();
  assert(ContCond);
  ContIfTrue = LoopBr->getSuccessor(0) == L->getHeader();

  // Build the sub-loops
  for (auto *SubL : *L) {
    auto *SubVL = new VLoop(LI, SubL, VPCtx, DA, CDA, LoopToVLoopMap);
    SubLoops.emplace_back(SubVL);
    SubVL->Parent = this;
    Depended |= SubVL->getDepended();
    Insts |= SubVL->Insts;
  }

  // Figure out the eta nodes
  for (PHINode &PN : Header->phis()) {
    assert(PN.getNumIncomingValues() == 2);
    Etas.try_emplace(&PN, PN.getIncomingValueForBlock(Preheader),
                     PN.getIncomingValueForBlock(Latch));
  }

  // Process the top-level instructions
  for (auto *BB : L->blocks()) {
    if (LI.getLoopFor(BB) != L)
      continue;
    for (auto &I : *BB) {
      Depended |= DA.getDepended(&I);
      TopLevelInsts.push_back(&I);
      Insts.set(VPCtx->getScalarId(&I));
    }
  }

  setSubtract(Depended, Insts);
}

llvm::Optional<EtaNode> VLoop::getEta(PHINode *PN) const {
  auto It = Etas.find(PN);
  if (It != Etas.end())
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

bool VLoop::isSafeToFuse(const VLoop *VL1, const VLoop *VL2,
                         ScalarEvolution &SE) {
  if (VL1 == VL2)
    return true;

  // The loops should be control-equivalent
  if (VL1->LoopCond != VL2->LoopCond)
    return false;

  // Loop level mismatch
  if (!VL1 || !VL2)
    return false;

  if (!haveIdenticalTripCounts(VL1->L, VL2->L, SE))
    return false;

  // Make sure the loops are independent
  if (VL1->Insts.anyCommon(VL2->Depended) ||
      VL2->Insts.anyCommon(VL1->Depended))
    return false;

  return isSafeToFuse(VL1->Parent, VL2->Parent, SE);
}

void VLoop::fuse(VLoop *VL1, VLoop *VL2, LoopToVLoopMapTy &LoopToVLoopMap) {
  assert(VL1 != VL2 && "can't fuse the same loop with itself");
  auto *Parent = VL1->Parent;
  if (Parent != VL2->Parent)
    fuse(VL1->Parent, VL2->Parent, LoopToVLoopMap);
  LoopToVLoopMap[VL2->L] = VL1;
  VL1->Insts |= VL2->Insts;
  VL1->Depended |= VL2->Depended;
  VL1->TopLevelInsts.append(VL2->TopLevelInsts);
  for (auto KV : VL2->Etas)
    VL1->Etas.insert(KV);

  assert(Parent);
  auto It = llvm::find_if(Parent->SubLoops, [VL2](std::unique_ptr<VLoop> &VL) {
    return VL.get() == VL2;
  });
  assert(It != Parent->SubLoops.end());
  Parent->SubLoops.erase(It);
}
