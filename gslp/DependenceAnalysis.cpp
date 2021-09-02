#include "DependenceAnalysis.h"
#include "VectorPackContext.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/Analysis/LazyValueInfo.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IntrinsicInst.h"

using namespace llvm;

static bool isLessThan(ScalarEvolution &SE, const SCEV *A, const SCEV *B) {
  return SE.isKnownNegative(SE.getMinusSCEV(A, B));
}

static const SCEV *refineWithRange(ScalarEvolution &SE, const SCEV *Expr,
                                   const ConstantRange &CR) {
  auto SMin = APInt::getSignedMinValue(CR.getBitWidth());
  auto UMin = APInt::getMinValue(CR.getBitWidth());
  auto SMax = APInt::getSignedMaxValue(CR.getBitWidth());
  auto UMax = APInt::getMaxValue(CR.getBitWidth());

  if (CR.getSignedMin() != SMax &&
      ConstantRange(CR.getSignedMin(), SMax).contains(CR))
    Expr = SE.getSMaxExpr(Expr, SE.getConstant(CR.getSignedMin()));
  if (CR.getUnsignedMin() != UMax &&
      ConstantRange(CR.getUnsignedMin(), UMax).contains(CR))
    Expr = SE.getUMaxExpr(Expr, SE.getConstant(CR.getUnsignedMin()));
  if (CR.getUpper() != SMin && ConstantRange(SMin, CR.getUpper()).contains(CR))
    Expr = SE.getSMinExpr(Expr, SE.getConstant(CR.getSignedMax()));
  if (UMin != CR.getUpper() && ConstantRange(UMin, CR.getUpper()).contains(CR))
    Expr = SE.getUMinExpr(Expr, SE.getConstant(CR.getUnsignedMax()));
  return Expr;
}

static const SCEV *
refineWithRanges(ScalarEvolution &SE, const SCEV *Expr,
                 const DenseMap<Value *, ConstantRange> &Ranges) {
  ValueToSCEVMapTy ValueToSCEV;
  for (auto &KV : Ranges)
    ValueToSCEV[KV.first] =
        refineWithRange(SE, SE.getSCEV(KV.first), KV.second);
  return SCEVParameterRewriter::rewrite(Expr, SE, ValueToSCEV);
}

namespace {
class UnknownSCEVCollector : public SCEVRewriteVisitor<UnknownSCEVCollector> {
  SmallPtrSetImpl<Value *> &Values;

public:
  UnknownSCEVCollector(ScalarEvolution &SE, SmallPtrSetImpl<Value *> &Values)
      : SCEVRewriteVisitor(SE), Values(Values) {}
  const SCEV *visitUnknown(const SCEVUnknown *Expr) {
    if (Expr->getType()->isIntegerTy())
      Values.insert(Expr->getValue());
    return Expr;
  }
};
} // namespace

static MemoryLocation getLocation(Instruction *I) {
  if (StoreInst *SI = dyn_cast<StoreInst>(I))
    return MemoryLocation::get(SI);
  if (LoadInst *LI = dyn_cast<LoadInst>(I))
    return MemoryLocation::get(LI);
  return MemoryLocation();
}

/// True if the instruction is not a volatile or atomic load/store.
static bool isSimple(Instruction *I) {
  if (LoadInst *LI = dyn_cast<LoadInst>(I))
    return LI->isSimple();
  if (StoreInst *SI = dyn_cast<StoreInst>(I))
    return SI->isSimple();
  if (MemIntrinsic *MI = dyn_cast<MemIntrinsic>(I))
    return !MI->isVolatile();
  return true;
}

static bool isAliased(Instruction *I1, Instruction *I2, AliasAnalysis &AA,
                      ScalarEvolution &SE, DominatorTree &DT, LoopInfo &LI,
                      LazyValueInfo &LVI) {
  auto *L1 = LI.getLoopFor(I1->getParent());
  auto *L2 = LI.getLoopFor(I2->getParent());
  bool InDifferentLoops = L1 && L2 && !L1->contains(L2) && !L2->contains(L1);

  auto *Ptr1 = getLoadStorePointerOperand(I1);
  auto *Ptr2 = getLoadStorePointerOperand(I2);
  if (Ptr1 && Ptr2 && !InDifferentLoops) {
    auto *Ptr1SCEV = SE.getSCEV(Ptr1);
    auto *Ptr2SCEV = SE.getSCEV(Ptr2);

    SmallPtrSet<Value *, 16> Unknowns;
    UnknownSCEVCollector UnknownCollector(SE, Unknowns);
    UnknownCollector.visit(Ptr1SCEV);
    UnknownCollector.visit(Ptr2SCEV);

    // Scan the function for CFG edges that dominates `I2` gives us range
    // information. Record and intersect those ranges.
    Function *F = I2->getParent()->getParent();
    DenseMap<Value *, ConstantRange> Ranges;
    for (auto &BB : *F) {
      for (auto *Succ : successors(&BB)) {
        if (!DT.dominates({&BB, Succ}, I2->getParent()))
          continue;
        for (Value *V : Unknowns) {
          // We only care about the unknown paremeters defined before both `I1`
          // and `I2`
          if (!DT.dominates(V, I2) || !DT.dominates(V, I1))
            continue;
          auto *I = dyn_cast<Instruction>(V);
          if (I && !DT.dominates(I, &BB))
            continue;
          auto CR = LVI.getConstantRangeOnEdge(V, &BB, Succ);
          if (CR.isFullSet())
            continue;
          auto Pair = Ranges.try_emplace(V, CR);
          if (!Pair.second) {
            ConstantRange &OldRange = Pair.first->second;
            OldRange = OldRange.intersectWith(CR);
          }
        }
      }
    }
    Ptr1SCEV = refineWithRanges(SE, Ptr1SCEV, Ranges);
    Ptr2SCEV = refineWithRanges(SE, Ptr2SCEV, Ranges);

    bool Lt = isLessThan(SE, Ptr1SCEV, Ptr2SCEV);
    bool Gt = isLessThan(SE, Ptr2SCEV, Ptr1SCEV);
    if (Lt || Gt) {
      // Assume WLOG that Ptr1 < Ptr2
      if (Gt) {
        std::swap(Ptr1SCEV, Ptr2SCEV);
        std::swap(Ptr1, Ptr2);
      }

      auto *Ty = cast<PointerType>(Ptr1->getType());
      auto AS = Ty->getAddressSpace();
      auto &DL = F->getParent()->getDataLayout();
      unsigned IndexWidth = DL.getIndexSizeInBits(AS);
      APInt Size(IndexWidth, DL.getTypeStoreSize(Ty->getElementType()));
      return SE.isKnownPositive(SE.getMinusSCEV(
          SE.getAddExpr(Ptr1SCEV, SE.getConstant(Size)), Ptr2SCEV));
    }
  }

  auto Loc1 = getLocation(I1);
  auto Loc2 = getLocation(I2);
  bool Aliased = true;
  if (Loc1.Ptr && Loc2.Ptr && isSimple(I1) && isSimple(I2)) {
    // Do the alias check.
    Aliased = AA.alias(Loc1, Loc2);
  }
  return Aliased;
}

bool LazyDependenceAnalysis::depends(Instruction *I1, Instruction *I2) {
  // No dependence if nobody writes
  if (!I1->mayWriteToMemory() && !I2->mayWriteToMemory())
    return false;

  // No dependence if no aliasing
  if (!isAliased(I1, I2, AA, SE, DT, LI, LVI))
    return false;

  // Fall back to DependenceInfo
  auto Dep = DI.depends(I1, I2, true);
  return Dep && !Dep->isInput();
}

// FIXME: change this to use LazyDependenceAnalysis
GlobalDependenceAnalysis::GlobalDependenceAnalysis(
    llvm::AliasAnalysis &AA, llvm::ScalarEvolution &SE, llvm::DominatorTree &DT,
    llvm::LoopInfo &LI, llvm::LazyValueInfo &LVI, llvm::Function *F,
    VectorPackContext *VPCtx) {

  SmallVector<Instruction *> MemRefs;

  // Scan the CFG in rpo (pred before succ) to discover the *direct* dependences
  // Mapping inst -> <users>
  DenseMap<Instruction *, SmallVector<Instruction *, 8>> Dependences;
  ReversePostOrderTraversal<Function *> RPO(F);
  DenseSet<Instruction *> Processed;
  for (auto *BB : RPO) {
    for (auto &I : *BB) {
      Processed.insert(&I);
      // Get the SSA dependences
      for (Value *V : I.operand_values()) {
        auto *OpInst = dyn_cast<Instruction>(V);
        // Ignore loop carried dependences, which can only come from phi nodes
        if (OpInst && DT.dominates(&I, OpInst)) {
          assert(isa<PHINode>(I));
          continue;
        }
        if (OpInst)
          Dependences[&I].push_back(OpInst);
      }

      if (!I.mayReadOrWriteMemory())
        continue;

      for (Instruction *PrevRef : MemRefs)
        if ((PrevRef->mayWriteToMemory() || I.mayWriteToMemory()) &&
            isAliased(&I, PrevRef, AA, SE, DT, LI, LVI))
          Dependences[&I].push_back(PrevRef);

      MemRefs.push_back(&I);
    }
  }

#if 1
  // Cycle detection
  DenseSet<Instruction *> Processing;
  DenseSet<Instruction *> Visited;
  std::function<void(Instruction *)> Visit = [&](Instruction *I) {
    assert(!Processing.count(I) && "CYCLE DETECTED IN DEP GRAPH");
    bool Inserted = Visited.insert(I).second;
    if (!Inserted)
      return;
    Processing.insert(I);
    for (auto *Src : Dependences[I])
      Visit(Src);
    Processing.erase(I);
  };
  for (auto &I : instructions(F))
    Visit(&I);
#endif

  // Now compute transitive closure in topological order
  for (auto *BB : RPO) {
    for (auto &I : *BB) {
      BitVector Depended = BitVector(VPCtx->getNumValues());
      for (auto *Src : Dependences[&I]) {
        assert(TransitiveClosure.count(Src));
        Depended.set(VPCtx->getScalarId(Src));
        Depended |= TransitiveClosure[Src];
      }
      TransitiveClosure[&I] = Depended;
    }
  }
}
