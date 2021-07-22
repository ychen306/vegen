#include "LoopFusion.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/Analysis/IVDescriptors.h" // RecurKind
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/PatternMatch.h"

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

      if (I.mayReadFromMemory() || I.mayWriteToMemory())
        Accesses.push_back(&I);
    }
  }
}

static bool checkLoop(Loop &L) {
  return L.getLoopPreheader() && L.getHeader() && L.getExitingBlock() &&
         L.getExitBlock() && L.getLoopLatch() && !L.isInvalid();
}

bool isUnsafeToFuse(Loop &L1, Loop &L2, ScalarEvolution &SE,
                    DependenceInfo &DI) {
  if (!checkLoop(L1) || !checkLoop(L2))
    return true;

  // Make sure the two loops have constant trip counts
  const SCEV *TripCount1 = SE.getBackedgeTakenCount(&L1);
  const SCEV *TripCount2 = SE.getBackedgeTakenCount(&L2);
  if (isa<SCEVCouldNotCompute>(TripCount1) ||
      isa<SCEVCouldNotCompute>(TripCount2) || TripCount1 != TripCount2)
    return true;

  DenseMap<Instruction *, RecurKind> ReductionKinds;

  // Collect the memory accesses
  SmallVector<Instruction *> Accesses1, Accesses2;
  bool UnsafeToFuse = false;
  collectMemoryAccesses(L1, Accesses1, ReductionKinds, UnsafeToFuse);
  if (UnsafeToFuse)
    return true;
  collectMemoryAccesses(L2, Accesses2, ReductionKinds, UnsafeToFuse);
  if (UnsafeToFuse)
    return true;

  // Check dependence
  for (auto *I1 : Accesses1)
    for (auto *I2 : Accesses2) {
      // We don't care about the dependence between a pair of reductions
      if (ReductionKinds.count(I1) && ReductionKinds.count(I2) &&
          ReductionKinds.lookup(I1) == ReductionKinds.lookup(I2))
        continue;
      auto Dep = DI.depends(I1, I2, true);
      if (Dep && !Dep->isInput())
        return true;
    }

  return false; // probably safe
}
