#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"

using namespace llvm;

static SmallVector<const Loop *, 4> getLoopNest(LoopInfo &LI, Instruction *I) {
  SmallVector<const Loop *, 4> LoopNest;
  for (auto *L = LI.getLoopFor(I->getParent()); L; L = L->getParentLoop())
    LoopNest.push_back(L);
  return LoopNest;
}

/// Take the address space operand from the Load/Store instruction.
/// Returns -1 if this is not a valid Load/Store instruction.
static unsigned getAddressSpaceOperand(Value *I) {
  if (LoadInst *L = dyn_cast<LoadInst>(I))
    return L->getPointerAddressSpace();
  if (StoreInst *S = dyn_cast<StoreInst>(I))
    return S->getPointerAddressSpace();
  return -1;
}

class AddRecLoopRewriter : public SCEVRewriteVisitor<AddRecLoopRewriter> {
public:
  using LoopToLoopMap = DenseMap<const Loop *, const Loop *>;

private:
  const LoopToLoopMap &Loops;
  bool Success;

public:
  AddRecLoopRewriter(ScalarEvolution &SE, const LoopToLoopMap &Loops)
      : SCEVRewriteVisitor<AddRecLoopRewriter>(SE), Loops(Loops),
        Success(true) {}

  static const SCEV *rewrite(ScalarEvolution &SE, const SCEV *Expr,
                             const LoopToLoopMap &Loops) {
    AddRecLoopRewriter Rewriter(SE, Loops);
    return Rewriter.visit(Expr);
  }

  const SCEV *visitAddRecExpr(const SCEVAddRecExpr *Expr) {
    if (!Success)
      return Expr;

    auto *OldLoop = Expr->getLoop();
    auto It = Loops.find(OldLoop);
    auto *NewLoop = It == Loops.end() ? OldLoop : It->second;

    SmallVector<const SCEV *> Operands;
    for (auto *Op : Expr->operands()) {
      Operands.push_back(visit(Op));
      if (!SE.isLoopInvariant(Operands.back(), NewLoop)) {
        Success = false;
        return Expr;
      }
    }

    return SE.getAddRecExpr(Operands, NewLoop, Expr->getNoWrapFlags());
  }
};

bool isEquivalent(Value *PtrA, Value *PtrB, ScalarEvolution &SE, LoopInfo &LI) {
  if (SE.getSCEV(PtrA) == SE.getSCEV(PtrB))
    return true;

  auto *A = dyn_cast<Instruction>(PtrA);
  auto *B = dyn_cast<Instruction>(PtrB);
  if (!A || !B)
    return false;

  auto LoopNest1 = getLoopNest(LI, A);
  auto LoopNest2 = getLoopNest(LI, B);
  if (LoopNest1.size() != LoopNest2.size())
    return false;

  const Loop *L1, *L2;
  AddRecLoopRewriter::LoopToLoopMap Loops;
  for (const auto &Pair : zip(LoopNest1, LoopNest2)) {
    std::tie(L1, L2) = Pair;
    if (SE.getBackedgeTakenCount(L1) != SE.getBackedgeTakenCount(L2))
      return false;
    Loops[L2] = L1;
  }

  const SCEV *PtrSCEVA = SE.getSCEV(PtrA);
  const SCEV *PtrSCEVB =
      AddRecLoopRewriter::rewrite(SE, SE.getSCEV(PtrB), Loops);
  return PtrSCEVA == PtrSCEVB;
}

// FIXME: get the loopnest of the *pointer*, not the loads

// llvm::isConsecutiveAccess modified to work for when A and B are in two
// separate loop nest
bool isConsecutive(Instruction *A, Instruction *B, const DataLayout &DL,
                   ScalarEvolution &SE, LoopInfo &LI) {
  auto LoopNest1 = getLoopNest(LI, A);
  auto LoopNest2 = getLoopNest(LI, B);
  if (LoopNest1.size() != LoopNest2.size())
    return false;

  const Loop *L1, *L2;
  AddRecLoopRewriter::LoopToLoopMap Loops;
  for (const auto &Pair : zip(LoopNest1, LoopNest2)) {
    std::tie(L1, L2) = Pair;
    if (SE.getBackedgeTakenCount(L1) != SE.getBackedgeTakenCount(L2))
      return false;
    Loops[L2] = L1;
  }

  Value *PtrA = getLoadStorePointerOperand(A);
  Value *PtrB = getLoadStorePointerOperand(B);
  if (PtrA->getType() != PtrB->getType())
    return false;

  unsigned ASA = getAddressSpaceOperand(A);
  unsigned ASB = getAddressSpaceOperand(B);

  // Check that the address spaces match and that the pointers are valid.
  if (!PtrA || !PtrB || (ASA != ASB))
    return false;

  // Make sure that A and B are different pointers.
  if (PtrA == PtrB)
    return false;

  unsigned IdxWidth = DL.getIndexSizeInBits(ASA);
  Type *Ty = cast<PointerType>(PtrA->getType())->getElementType();

  APInt OffsetA(IdxWidth, 0), OffsetB(IdxWidth, 0);
  PtrA = PtrA->stripAndAccumulateInBoundsConstantOffsets(DL, OffsetA);
  PtrB = PtrB->stripAndAccumulateInBoundsConstantOffsets(DL, OffsetB);

  // Retrieve the address space again as pointer stripping now tracks through
  // `addrspacecast`.
  ASA = cast<PointerType>(PtrA->getType())->getAddressSpace();
  ASB = cast<PointerType>(PtrB->getType())->getAddressSpace();
  // Check that the address spaces match and that the pointers are valid.
  if (ASA != ASB)
    return false;

  IdxWidth = DL.getIndexSizeInBits(ASA);
  OffsetA = OffsetA.sextOrTrunc(IdxWidth);
  OffsetB = OffsetB.sextOrTrunc(IdxWidth);

  APInt Size(IdxWidth, DL.getTypeStoreSize(Ty));

  //  OffsetDelta = OffsetB - OffsetA;
  const SCEV *OffsetSCEVA = SE.getConstant(OffsetA);
  const SCEV *OffsetSCEVB = SE.getConstant(OffsetB);
  const SCEV *OffsetDeltaSCEV = SE.getMinusSCEV(OffsetSCEVB, OffsetSCEVA);
  const APInt &OffsetDelta = cast<SCEVConstant>(OffsetDeltaSCEV)->getAPInt();

  // Check if they are based on the same pointer. That makes the offsets
  // sufficient.
  if (PtrA == PtrB)
    return OffsetDelta == Size;

  // Compute the necessary base pointer delta to have the necessary final delta
  // equal to the size.
  // BaseDelta = Size - OffsetDelta;
  const SCEV *SizeSCEV = SE.getConstant(Size);
  const SCEV *BaseDelta = SE.getMinusSCEV(SizeSCEV, OffsetDeltaSCEV);

  // Otherwise compute the distance with SCEV between the base pointers.
  const SCEV *PtrSCEVA = SE.getSCEV(PtrA);
  const SCEV *PtrSCEVB =
      AddRecLoopRewriter::rewrite(SE, SE.getSCEV(PtrB), Loops);
  const SCEV *X = SE.getAddExpr(PtrSCEVA, BaseDelta);
  return X == PtrSCEVB;
}
