#include "LocalDependenceAnalysis.h"
#include "VectorPackContext.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/IR/Function.h"

using namespace llvm;

static MemoryLocation getLocation(Instruction *I, AliasAnalysis *AA) {
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

static bool isAliased(const MemoryLocation &Loc1, Instruction *Inst1,
               Instruction *Inst2, AliasAnalysis *AA) {
  MemoryLocation Loc2 = getLocation(Inst2, AA);
  bool Aliased = true;
  if (Loc1.Ptr && Loc2.Ptr && isSimple(Inst1) && isSimple(Inst2)) {
    // Do the alias check.
    Aliased = AA->alias(Loc1, Loc2);
  }
  return Aliased;
}

LocalDependenceAnalysis::LocalDependenceAnalysis(llvm::AliasAnalysis *AA,
                                                 llvm::BasicBlock *BB,
                                                 VectorPackContext *VPCtx)
    : BB(BB), VPCtx(VPCtx) {
  std::vector<Instruction *> MemRefs;
  // Build the local dependence graph
  for (Instruction &I : *BB) {
    // PHINodes do not introduce any local dependence
    if (isa<PHINode>(&I))
      continue;

    for (Value *Operand : I.operands()) {
      if (auto *I2 = dyn_cast<Instruction>(Operand)) {
        if (!isa<PHINode>(I2) && I2->getParent() == BB) {
          Dependencies[&I].push_back(I2);
        }
      }
    }
    if (I.mayReadOrWriteMemory()) {
      MemoryLocation Loc = getLocation(&I, AA);
      // check dependence with preceding loads and stores
      for (auto *PrevRef : MemRefs) {
        if ((PrevRef->mayWriteToMemory() || I.mayWriteToMemory()) &&
            isAliased(Loc, &I, PrevRef, AA))
          Dependencies[&I].push_back(PrevRef);
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
    for (auto *Src : Dependencies[I])
      Visit(Src);
    Processing.erase(I);
  };
  for (auto &I : *BB)
    Visit(&I);
#endif

  // Now compute transitive closure in topological order,
  // which we don't need to compute because the basic block order is a valid
  // one
  for (auto &I : *BB) {
    BitVector Depended = BitVector(VPCtx->getNumValues());
    for (auto *Src : Dependencies[&I]) {
      assert(TransitiveClosure.count(Src));
      Depended.set(VPCtx->getScalarId(Src));
      unsigned Count = Depended.count();
      Depended |= TransitiveClosure[Src];
    }

    TransitiveClosure[&I] = Depended;
  }
}
