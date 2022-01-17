#include "DependenceAnalysis.h"
#include "VectorPackContext.h"
#include "LoopAwareRPO.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/Support/CommandLine.h"

using namespace llvm;
using namespace PatternMatch;

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

static const Loop *getLoopForPointer(LoopInfo &LI, Value *Ptr) {
  auto *I = dyn_cast<Instruction>(Ptr);
  if (!I)
    return nullptr;
  return LI.getLoopFor(I->getParent());
}

// Copied from SCEV AA
static Value *getBaseValue(const SCEV *S) {
  if (const SCEVAddRecExpr *AR = dyn_cast<SCEVAddRecExpr>(S)) {
    // In an addrec, assume that the base will be in the start, rather
    // than the step.
    return getBaseValue(AR->getStart());
  } else if (const SCEVAddExpr *A = dyn_cast<SCEVAddExpr>(S)) {
    // If there's a pointer operand, it'll be sorted at the end of the list.
    const SCEV *Last = A->getOperand(A->getNumOperands() - 1);
    if (Last->getType()->isPointerTy())
      return getBaseValue(Last);
  } else if (const SCEVUnknown *U = dyn_cast<SCEVUnknown>(S)) {
    // This is a leaf node.
    return U->getValue();
  }
  // No Identified object found.
  return nullptr;
}

static bool isAliased(Instruction *I1, Instruction *I2, AliasAnalysis &AA,
                      ScalarEvolution &SE, LoopInfo &LI,
                      LazyValueInfo &LVI) {
  auto Loc1 = getLocation(I1);
  auto Loc2 = getLocation(I2);
  Function *F = I1->getParent()->getParent();
  if (Loc1.Ptr && Loc2.Ptr && isSimple(I1) && isSimple(I2)) {
    // Do the alias check.
    auto Result = AA.alias(Loc1, Loc2);
    if (Result != MayAlias)
      return Result;
  }

  auto *Ptr1 = getLoadStorePointerOperand(I1);
  auto *Ptr2 = getLoadStorePointerOperand(I2);
  if (!Ptr1 || !Ptr2)
    return true;

  auto *Ptr1SCEV = SE.getSCEV(Ptr1);
  auto *Ptr2SCEV = SE.getSCEV(Ptr2);

  auto *Base1 = getBaseValue(Ptr1SCEV);
  auto *Base2 = getBaseValue(Ptr2SCEV);
  if (Base1 && Base2 && Base1 != Base2)
    return AA.alias(MemoryLocation::getBeforeOrAfter(Base1),
                    MemoryLocation::getBeforeOrAfter(Base2));

  // The check below assumes that the loops used by the two SCEVs are totally
  // ordered. Check it!
  struct FindUsedLoops {
    FindUsedLoops(SmallVectorImpl<const Loop *> &LoopsUsed)
        : LoopsUsed(LoopsUsed) {}
    SmallVectorImpl<const Loop *> &LoopsUsed;
    bool follow(const SCEV *S) {
      if (auto *AR = dyn_cast<SCEVAddRecExpr>(S))
        LoopsUsed.push_back(AR->getLoop());
      return true;
    }

    bool isDone() const { return false; }
  };

  SmallVector<const Loop *> Loops;
  FindUsedLoops LoopFinder(Loops);
  SCEVTraversal<FindUsedLoops> LoopCollector(LoopFinder);

  LoopCollector.visitAll(Ptr1SCEV);
  LoopCollector.visitAll(Ptr2SCEV);

  auto CompareLoops = [](const Loop *L1, const Loop *L2) {
    return L1 == L2 || L1->contains(L2);
  };
  stable_sort(Loops, CompareLoops);
  for (int i = 0; i < (int)Loops.size() - 1; i++)
    if (!CompareLoops(Loops[i], Loops[i + 1]))
      return true;

  bool Lt = isLessThan(SE, Ptr1SCEV, Ptr2SCEV);
  bool Gt = isLessThan(SE, Ptr2SCEV, Ptr1SCEV);
  if (!Lt && !Gt)
    return true;
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
  return SE.isKnownPositive(
      SE.getMinusSCEV(SE.getAddExpr(Ptr1SCEV, SE.getConstant(Size)), Ptr2SCEV));

  return true;
}

// FIXME: change this to use LazyDependenceAnalysis
GlobalDependenceAnalysis::GlobalDependenceAnalysis(
    AliasAnalysis &AA, ScalarEvolution &SE, LoopInfo &LI,
    LazyValueInfo &LVI, Function *F, VectorPackContext *VPCtx, bool NoAlias) : VPCtx(VPCtx) {

  SmallVector<Instruction *> MemRefs;

  // Scan the CFG in rpo (pred before succ) to discover the *direct* dependences
  // Mapping inst -> <users>
  DenseMap<Instruction *, SmallVector<Instruction *, 8>> Dependences;
  SmallVector<BasicBlock *> RPO;
  computeRPO(F, LI, RPO);

  DenseSet<Instruction *> Processed;
  for (auto *BB : RPO) {
    auto *L = LI.getLoopFor(BB);
    bool IsHeader = LI.isLoopHeader(BB);
    assert(!IsHeader || L);
    for (auto &I : *BB) {
      Processed.insert(&I);
      // Get the SSA dependences
      for (Value *V : I.operand_values()) {
        auto *OpInst = dyn_cast<Instruction>(V);
        if (!OpInst)
          continue;
        // Ignore loop carried dependences, which can only come from loop-header phi nodes
        bool IsLoopCarriedDep = IsHeader && isa<PHINode>(&I) && L->contains(OpInst);
        if (!IsLoopCarriedDep)
          Dependences[&I].push_back(OpInst);
      }

      if (m_Intrinsic<Intrinsic::experimental_noalias_scope_decl>(m_Value()).match(&I) ||
          m_Intrinsic<Intrinsic::lifetime_start>(m_Value()).match(&I) ||
          m_Intrinsic<Intrinsic::lifetime_end>(m_Value()).match(&I))
        continue;

      if (!isa<ReturnInst>(&I) && (NoAlias || !I.mayReadOrWriteMemory()))
        continue;

      for (Instruction *PrevRef : MemRefs)
        if ((isa<ReturnInst>(PrevRef) || PrevRef->mayWriteToMemory() ||
             I.mayWriteToMemory()) &&
            isAliased(&I, PrevRef, AA, SE, LI, LVI))
          Dependences[&I].push_back(PrevRef);

      MemRefs.push_back(&I);
    }
  }

#ifndef NDEBUG
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
  for (auto *BB : RPO)
    for (auto &I : *BB)
      addDependences(&I, Dependences[&I]);
}

void GlobalDependenceAnalysis::addDependences(Instruction *I, ArrayRef<Instruction *> Deps) {
  assert(VPCtx->isKnownValue(I));
  BitVector Depended(VPCtx->getNumValues());
  for (auto *Dep: Deps) {
    Depended.set(VPCtx->getScalarId(Dep));
    if (TransitiveClosure.count(Dep))
      Depended |= TransitiveClosure[Dep];
  }
  TransitiveClosure[I] = Depended;
}

void GlobalDependenceAnalysis::addInstruction(Instruction *I) {
  SmallVector<Instruction *, 2> Deps;
  for (Value *O : I->operands())
    if (auto *OI = dyn_cast<Instruction>(O))
      Deps.push_back(OI);
  addDependences(I, Deps);
}
