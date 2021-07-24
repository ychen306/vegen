#include "LoopFusion.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/Analysis/IVDescriptors.h" // RecurKind
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/Transforms/Utils/CodeMoverUtils.h"

using namespace llvm;

namespace {

template <typename PatternTy, typename ValueTy> struct Capture_match {
  PatternTy P;
  ValueTy *&V;

  Capture_match(PatternTy P, ValueTy *&V) : P(P), V(V) {}

  template <typename OpTy> bool match(OpTy *Op) {
    if (P.match(Op)) {
      V = cast<ValueTy>(Op);
      return true;
    }
    return false;
  }
};

template <typename PatternTy, typename ValueTy>
Capture_match<PatternTy, ValueTy> m_Capture(PatternTy P, ValueTy *&V) {
  return Capture_match<PatternTy, ValueTy>(P, V);
}

} // namespace

static Optional<RecurKind> matchReduction(StoreInst *SI, LoadInst *&LI) {
  Value *V = SI->getValueOperand();
  using namespace llvm::PatternMatch;

  LI = nullptr;
  auto TheLoad =
      m_Capture(m_OneUse(m_Load(m_Specific(SI->getPointerOperand()))), LI);

  RecurKind Kind;
  if (match(V, m_c_Add(TheLoad, m_Value())))
    Kind = RecurKind::Add;
  else if (match(V, m_c_Mul(TheLoad, m_Value())))
    Kind = RecurKind::Mul;
  else if (match(V, m_c_And(TheLoad, m_Value())))
    Kind = RecurKind::And;
  else if (match(V, m_c_Or(TheLoad, m_Value())))
    Kind = RecurKind::Or;
  else if (match(V, m_c_Xor(TheLoad, m_Value())))
    Kind = RecurKind::Xor;
  else if (match(V, m_c_FAdd(TheLoad, m_Value())))
    Kind = RecurKind::FAdd;
  else if (match(V, m_c_FMul(TheLoad, m_Value())))
    Kind = RecurKind::FMul;

  // there's no m_c_FMin/Max
  else if (match(V, m_FMin(TheLoad, m_Value())))
    Kind = RecurKind::FMax;
  else if (match(V, m_FMax(TheLoad, m_Value())))
    Kind = RecurKind::FMin;
  else if (match(V, m_FMin(m_Value(), TheLoad)))
    Kind = RecurKind::FMax;
  else if (match(V, m_FMax(m_Value(), TheLoad)))
    Kind = RecurKind::FMin;

  else if (match(V, m_c_SMax(TheLoad, m_Value())))
    Kind = RecurKind::SMax;
  else if (match(V, m_c_SMin(TheLoad, m_Value())))
    Kind = RecurKind::SMin;
  else if (match(V, m_c_UMax(TheLoad, m_Value())))
    Kind = RecurKind::UMax;
  else if (match(V, m_c_UMin(TheLoad, m_Value())))
    Kind = RecurKind::UMin;
  else
    return None;

  assert(LI);
  return Kind;
}

static void
collectMemoryAccesses(Loop &L, SmallVectorImpl<Instruction *> &Accesses,
                      DenseMap<Instruction *, RecurKind> &ReductionKinds,
                      bool &UnsafeToFuse) {
  for (auto *BB : L.blocks()) {
    if (BB->hasAddressTaken()) {
      UnsafeToFuse = true;
      return;
    }

    for (auto &I : *BB) {
      if (I.mayThrow()) {
        UnsafeToFuse = true;
        return;
      }

      if (isa<CallBase>(&I) && I.mayHaveSideEffects()) {
        UnsafeToFuse = true;
        return;
      }

      auto *LI = dyn_cast<LoadInst>(&I);
      auto *SI = dyn_cast<StoreInst>(&I);
      if ((LI && LI->isVolatile()) || (SI && SI->isVolatile())) {
        UnsafeToFuse = true;
        return;
      }

      if (SI) {
        LoadInst *LI;
        if (Optional<RecurKind> Kind = matchReduction(SI, LI)) {
          ReductionKinds[SI] = *Kind;
          ReductionKinds[LI] = *Kind;
        }
      }

      if (I.mayReadOrWriteMemory())
        Accesses.push_back(&I);
    }
  }
}

static bool checkLoop(Loop &L) {
  return L.getLoopPreheader() && L.getHeader() && L.getExitingBlock() &&
         L.getExitBlock() && L.getLoopLatch() && L.isRotatedForm() &&
         !L.isInvalid();
}

// Return true is *independent*
static bool checkDependencies(Loop &L1, Loop &L2, DependenceInfo &DI) {
  // Collect the memory accesses
  SmallVector<Instruction *> Accesses1, Accesses2;
  DenseMap<Instruction *, RecurKind> ReductionKinds;
  bool UnsafeToFuse = false;
  collectMemoryAccesses(L1, Accesses1, ReductionKinds, UnsafeToFuse);
  if (UnsafeToFuse)
    return false;
  collectMemoryAccesses(L2, Accesses2, ReductionKinds, UnsafeToFuse);
  if (UnsafeToFuse)
    return false;

  // Check dependence
  for (auto *I1 : Accesses1)
    for (auto *I2 : Accesses2) {
      // We don't care about the dependence between a pair of reductions
      if (ReductionKinds.count(I1) && ReductionKinds.count(I2) &&
          ReductionKinds.lookup(I1) == ReductionKinds.lookup(I2))
        continue;
      auto Dep = DI.depends(I1, I2, true);
      if (Dep && !Dep->isInput())
        return false;
    }
  return true;
}

static bool isUsedByLoop(Instruction *I, Loop &L, DependenceInfo &DI) {
  SmallVector<Instruction *> LoopReads;
  for (auto *BB : L.blocks())
    for (auto &I : *BB)
      if (I.mayReadFromMemory())
        LoopReads.push_back(&I);

  DenseSet<Instruction *> Visited; // Deal with cycles resulted from PHIs
  std::function<bool(Instruction *)> IsUsed = [&](Instruction *V) -> bool {
    Visited.insert(I);

    if (L.contains(I->getParent()))
      return true;

    if (I->mayWriteToMemory())
      for (auto *I2 : LoopReads)
        if (DI.depends(I, I2, true))
          return true;

    for (User *U : I->users()) {
      auto *UI = dyn_cast<Instruction>(U);
      if (Visited.count(UI))
        continue;
      if (UI && IsUsed(UI))
        return true;
    }

    return false;
  };

  return IsUsed(I);
}

static BasicBlock *getLoopEntry(Loop &L) {
  return L.isGuarded() ? L.getLoopGuardBranch()->getParent()
                       : L.getLoopPreheader();
}

bool isUnsafeToFuse(Loop &L1, Loop &L2, ScalarEvolution &SE, DependenceInfo &DI,
                    DominatorTree &DT, PostDominatorTree &PDT) {
  if (!checkLoop(L1) || !checkLoop(L2)) {
    errs() << "Loops don't have the right shape\n";
    return true;
  }

  if (L1.getLoopDepth() != L2.getLoopDepth()) {
    errs() << "Loops have different nesting level\n";
    return true;
  }

  // Make sure the two loops have constant trip counts
  const SCEV *TripCount1 = SE.getBackedgeTakenCount(&L1);
  const SCEV *TripCount2 = SE.getBackedgeTakenCount(&L2);
  if (isa<SCEVCouldNotCompute>(TripCount1) ||
      isa<SCEVCouldNotCompute>(TripCount2) || TripCount1 != TripCount2) {
    errs() << "Loops may have divergent trip count\n";
    return true;
  }

  Loop *L1Parent = L1.getParentLoop();
  Loop *L2Parent = L2.getParentLoop();
  // If L1 and L2 are nested inside other loops, those loops also need to be
  // fused
  if (!L1.isOutermost() && L1Parent != L2Parent) {
    if (isUnsafeToFuse(*L1.getParentLoop(), *L2.getParentLoop(), SE, DI, DT,
                       PDT)) {
      errs() << "Parent loops can't be fused\n";
      return true;
    }
    // TODO: maybe support convergent control flow?
    // For how, don't fuse nested loops that are conditionally executed
    // (since it's harder to prove they are executed together)
    if (!isControlFlowEquivalent(*L1.getParentLoop()->getHeader(), *getLoopEntry(L1), DT, PDT) ||
        !isControlFlowEquivalent(*L2.getParentLoop()->getHeader(), *getLoopEntry(L2), DT, PDT)) {
      errs() << "Can't fuse conditional nested loop\n";
      return true;
    }
  } else  {
    if (!checkDependencies(L1, L2, DI)) {
      errs() << "Loops are dependent (memory)\n";
      return true;
    }

    if (!isControlFlowEquivalent(*L1.getLoopPreheader(), *L2.getLoopPreheader(), DT, PDT)) {
      errs() << "Loops are not control flow equivalent\n";
      return true;
    }
  }

  // Check if one loop computes any SSA values that are used by another loop
  if (!L1.isLCSSAForm(DT) || !L2.isLCSSAForm(DT)) {
    errs() << "Loops are not in LCSSA\n";
    return true;
  }

  for (PHINode &PN : L1.getExitBlock()->phis())
    if (isUsedByLoop(&PN, L2, DI)) {
      errs() << "Loops are dependent (ssa)\n";
      return true;
    }
  for (PHINode &PN : L2.getExitBlock()->phis())
    if (isUsedByLoop(&PN, L1, DI)) {
      errs() << "Loops are dependent (ssa)\n";
      return true;
    }

  return false; // *probably* safe
}
