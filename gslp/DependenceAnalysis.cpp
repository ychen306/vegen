#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/Analysis/LazyValueInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/IR/Dominators.h"

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

static Value *getLoadStorePointer(Instruction *I) {
  if (auto *LI = dyn_cast<LoadInst>(I))
    return LI->getPointerOperand();
  if (auto *SI = dyn_cast<StoreInst>(I))
    return SI->getPointerOperand();
  return nullptr;
}

bool depends(Instruction *Def, Instruction *Use, DependenceInfo &DI,
             ScalarEvolution &SE, DominatorTree &DT, LazyValueInfo *LVI) {
  if (!Def->mayWriteToMemory() && !Use->mayWriteToMemory())
    return false;

  auto *Ptr1 = getLoadStorePointer(Def);
  auto *Ptr2 = getLoadStorePointer(Use);
  if (LVI && Ptr1 && Ptr2) {
    auto *Ptr1SCEV = SE.getSCEV(Ptr1);
    auto *Ptr2SCEV = SE.getSCEV(Ptr2);

    SmallPtrSet<Value *, 16> Unknowns;
    UnknownSCEVCollector UnknownCollector(SE, Unknowns);
    UnknownCollector.visit(Ptr1SCEV);
    UnknownCollector.visit(Ptr2SCEV);

    // Scan the function for CFG edges that dominates `Use` gives us range
    // information. Record and intersect those ranges.
    Function *F = Use->getParent()->getParent();
    DenseMap<Value *, ConstantRange> Ranges;
    for (auto &BB : *F) {
      for (auto *Succ : successors(&BB)) {
        if (!DT.dominates({&BB, Succ}, Use->getParent()))
          continue;
        for (auto *V : Unknowns) {
          // We only care about the unknown paremeters defined before both `Def`
          // and `Use`
          if (!DT.dominates(V, Use) || !DT.dominates(V, Def))
            continue;
          auto CR = LVI->getConstantRangeOnEdge(V, &BB, Succ);
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

  auto Dep = DI.depends(Def, Use, true);
  return Dep && !Dep->isInput();
}
