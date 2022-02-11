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
#include "llvm/Analysis/DependenceAnalysis.h"


using namespace llvm;
using namespace PatternMatch;

static bool isLessThan(ScalarEvolution &SE, const SCEV *A, const SCEV *B) {
  return SE.isKnownNegative(SE.getMinusSCEV(A, B));
}

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

  DependenceInfo DI(F, &AA, &SE, &LI);

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

        // User of a header phi that's OUTSIDE of that loop
        // should take that recursive dep. into account
        auto *PN = dyn_cast<PHINode>(OpInst);
        if (!PN)
          continue;
        auto *PNLoop = LI.getLoopFor(PN->getParent());
        if (PNLoop && PN->getParent() == PNLoop->getHeader() && !PNLoop->contains(&I)) {
          assert(PNLoop->getLoopLatch());
          if (auto *I2 = dyn_cast<Instruction>(PN->getIncomingValueForBlock(PNLoop->getLoopLatch())))
            Dependences[&I].push_back(I2);
        }
      }

      if (m_Intrinsic<Intrinsic::experimental_noalias_scope_decl>(m_Value()).match(&I) ||
          m_Intrinsic<Intrinsic::lifetime_start>(m_Value()).match(&I) ||
          m_Intrinsic<Intrinsic::lifetime_end>(m_Value()).match(&I))
        continue;

      if (!isa<ReturnInst>(&I) && (NoAlias || !I.mayReadOrWriteMemory()))
        continue;

      for (Instruction *PrevRef : MemRefs)
        if ((isa<ReturnInst>(PrevRef) || PrevRef->mayWriteToMemory() ||
              I.mayWriteToMemory())) {
          auto *L1 = LI.getLoopFor(PrevRef->getParent());
          auto *L2 = LI.getLoopFor(I.getParent());
          if (L1 == L2 && !isAliased(PrevRef, &I, AA, SE, LI, LVI))
            continue;
          auto Dep = DI.depends(PrevRef, &I, true);
          if (Dep && Dep->isOrdered())
            Dependences[&I].push_back(PrevRef);
        }

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
