#define DEBUG_TYPE "vegen"

#include "CodeMotionUtil.h" // haveIdenticalTripCounts
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"

using namespace llvm;

ALWAYS_ENABLED_STATISTIC(NumConsecChecks, "Number of consecutive checks");
ALWAYS_ENABLED_STATISTIC(NumEquivChecks, "Number of load-equivalence checks");

static SmallVector<const Loop *, 4> getLoopNest(LoopInfo &LI, Value *V) {
  auto *I = dyn_cast<Instruction>(V);
  if (!I)
    return {};

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
      if (!SE.isAvailableAtLoopEntry(Operands.back(), NewLoop)) {
        Success = false;
        return Expr;
      }
    }

    return SE.getAddRecExpr(Operands, NewLoop, Expr->getNoWrapFlags());
  }
};

bool isEquivalent(Value *PtrA, Value *PtrB, ScalarEvolution &SE, LoopInfo &LI) {
  NumEquivChecks++;

  if (SE.getSCEV(PtrA) == SE.getSCEV(PtrB))
    return true;

  auto *A = dyn_cast<Instruction>(PtrA);
  auto *B = dyn_cast<Instruction>(PtrB);
  if (!A || !B)
    return false;

  if (PtrA->getType() != PtrB->getType())
    return false;

  // FIXME: factor this part out of isEquivalent and isConsecutive
  auto LoopNest1 = getLoopNest(LI, A);
  auto LoopNest2 = getLoopNest(LI, B);
  if (LoopNest1.size() != LoopNest2.size())
    return false;

  const Loop *L1, *L2;
  AddRecLoopRewriter::LoopToLoopMap Loops;
  for (const auto &Pair : zip(LoopNest1, LoopNest2)) {
    std::tie(L1, L2) = Pair;
    if (!haveIdenticalTripCounts(L1, L2, SE))
      return false;
    Loops[L2] = L1;
  }

  const SCEV *PtrSCEVA = SE.getSCEV(PtrA);
  const SCEV *PtrSCEVB =
      AddRecLoopRewriter::rewrite(SE, SE.getSCEV(PtrB), Loops);
  return PtrSCEVA == PtrSCEVB;
}

void fingerprintSCEV(ScalarEvolution &SE, const SCEV *Expr,
                     SmallVectorImpl<int64_t> &Fingerprints, unsigned N) {
  constexpr int64_t FakeSize = 128;

  class SCEVFingerprinter : public SCEVRewriteVisitor<SCEVFingerprinter> {
    unsigned Iter;

  public:
    SCEVFingerprinter(ScalarEvolution &SE, unsigned Iter)
        : SCEVRewriteVisitor(SE), Iter(Iter) {}

    const SCEV *visitAddRecExpr(const SCEVAddRecExpr *Expr) {
      SmallVector<const SCEV *, 4> Operands;
      for (auto *Op : Expr->operands())
        Operands.push_back(visit(Op));
      auto *Rec = cast<SCEVAddRecExpr>(
          SE.getAddRecExpr(Operands, Expr->getLoop(), Expr->getNoWrapFlags()));
      return Rec->evaluateAtIteration(SE.getConstant(APInt(64, Iter)), SE);
    }

    const SCEV *visitUnknown(const SCEVUnknown *Expr) {
      return SE.getConstant(Expr->getType(), FakeSize);
    }
  };

  Fingerprints.resize(N);
  for (unsigned i = 0; i < N; i++) {
    SCEVFingerprinter Fingerprinter(SE, i);
    Fingerprints[i] = cast<SCEVConstant>(Fingerprinter.visit(Expr))
                          ->getAPInt()
                          .getLimitedValue();
  }
}

// llvm::isConsecutiveAccess modified to work for when A and B are in two
// separate loop nest
bool isConsecutive(Instruction *A, Instruction *B, const DataLayout &DL,
                   ScalarEvolution &SE, LoopInfo &LI) {
  NumConsecChecks++;
  Value *PtrA = getLoadStorePointerOperand(A);
  Value *PtrB = getLoadStorePointerOperand(B);

  if (!PtrA || !PtrB)
    return false;

  unsigned ASA = getAddressSpaceOperand(A);
  unsigned ASB = getAddressSpaceOperand(B);

  auto LoopNest1 = getLoopNest(LI, PtrA);
  auto LoopNest2 = getLoopNest(LI, PtrB);
  if (LoopNest1.size() != LoopNest2.size())
    return false;

  const Loop *L1, *L2;
  AddRecLoopRewriter::LoopToLoopMap Loops;
  for (const auto &Pair : zip(LoopNest1, LoopNest2)) {
    std::tie(L1, L2) = Pair;
    if (L1 == L2)
      continue;
    if (!haveIdenticalTripCounts(L1, L2, SE))
      return false;
    Loops[L2] = L1;
  }

  // Check that the address spaces match and that the pointers are valid.
  if (!PtrA || !PtrB || (ASA != ASB))
    return false;

  if (PtrA->getType() != PtrB->getType())
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
  const SCEV *PtrSCEVB = SE.getSCEV(PtrB);

  if (!Loops.empty())
    AddRecLoopRewriter::rewrite(SE, PtrSCEVB, Loops);
  const SCEV *X = SE.getAddExpr(PtrSCEVA, BaseDelta);
  return X == PtrSCEVB;
}

std::vector<std::pair<Instruction *, Instruction *>>
findConsecutiveAccesses(ScalarEvolution &SE, const DataLayout &DL, LoopInfo &LI,
                        ArrayRef<Instruction *> Accesses,
                        EquivalenceClasses<Instruction *> &EquivalentAccesses,
                        unsigned NumFingerprints) {
  if (Accesses.empty())
    return {};

  DenseMap<int64_t, std::vector<Instruction *>> FingerprintsToAccesses;
  DenseMap<Instruction *, SmallVector<int64_t, 4>> AccessToFingerprints;

  // Figure out size of the accesses here
  Value *Ptr = getLoadStorePointerOperand(Accesses.front());
  Type *Ty = cast<PointerType>(Ptr->getType())->getElementType();
  int64_t Size = DL.getTypeStoreSize(Ty);

  std::vector<std::pair<Instruction *, Instruction *>> ConsecutiveAccesses;

  for (Instruction *I : Accesses) {
    Value *Ptr = getLoadStorePointerOperand(I);
    assert(Ptr);
    SmallVector<int64_t, 4> Fingerprints;
    auto *PtrSCEV = SE.getSCEV(Ptr);
    fingerprintSCEV(SE, PtrSCEV, Fingerprints, NumFingerprints);

    int64_t Left = Fingerprints.front() - Size;
    for (Instruction *LeftI : FingerprintsToAccesses.lookup(Left)) {
      ArrayRef<int64_t> LeftFingerprints = AccessToFingerprints[LeftI];
      if (!all_of(zip(LeftFingerprints, Fingerprints), [Size](auto Pair) {
            return std::get<0>(Pair) + Size == std::get<1>(Pair);
          }))
        continue;
      if (isConsecutive(LeftI, I, DL, SE, LI))
        ConsecutiveAccesses.emplace_back(LeftI, I);
    }

    for (Instruction *I2 : FingerprintsToAccesses.lookup(Fingerprints.front())) {
      ArrayRef<int64_t> Fingerprints2 = AccessToFingerprints[I2];
      if (!all_of(zip(Fingerprints2, Fingerprints), [Size](auto Pair) {
            return std::get<0>(Pair) == std::get<1>(Pair);
          }))
        continue;
      if (isEquivalent(getLoadStorePointerOperand(I), getLoadStorePointerOperand(I2), SE, LI))
        EquivalentAccesses.unionSets(I, I2);
    }


    int64_t Right = Fingerprints.front() + Size;
    for (Instruction *RightI : FingerprintsToAccesses.lookup(Right)) {
      ArrayRef<int64_t> RightFingerprints = AccessToFingerprints[RightI];
      if (!all_of(zip(RightFingerprints, Fingerprints), [Size](auto Pair) {
            return std::get<0>(Pair) == std::get<1>(Pair) + Size;
          }))
        continue;
      if (isConsecutive(RightI, I, DL, SE, LI))
        ConsecutiveAccesses.emplace_back(RightI, I);
    }

    FingerprintsToAccesses[Fingerprints.front()].push_back(I);
    AccessToFingerprints.try_emplace(I, std::move(Fingerprints));
  }

  return ConsecutiveAccesses;
}
