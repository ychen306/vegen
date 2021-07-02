#include "LocalDependenceAnalysis.h"
#include "VectorPackContext.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/VectorUtils.h"
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

static Value *getLoadStorePointer(Instruction *I) {
  if (auto *LI = dyn_cast<LoadInst>(I))
    return LI->getPointerOperand();
  if (auto *SI = dyn_cast<StoreInst>(I))
    return SI->getPointerOperand();
  return nullptr;
}

static bool overlaps(APInt Lo1, APInt Hi1, APInt Lo2, APInt Hi2) {
  return Hi1.sge(Lo2);
}

static bool isAliased(const MemoryLocation &Loc1, Instruction *Inst1,
                      Instruction *Inst2, AliasAnalysis *AA,
                      const DataLayout *DL) {
  // Hack to get around the fact that AA sometimes return
  // MayAlias for consecutive accesses...
  auto *Ptr1 = getLoadStorePointer(Inst1);
  auto *Ptr2 = getLoadStorePointer(Inst2);
  if (Ptr1 && Ptr2) {
    auto *Ty1 = cast<PointerType>(Ptr1->getType());
    auto *Ty2 = cast<PointerType>(Ptr1->getType());
    if (Ty1->getAddressSpace() != Ty2->getAddressSpace())
      return false;

    auto AS = Ty1->getAddressSpace();
    unsigned IndexWidth = DL->getIndexSizeInBits(AS);

    APInt Offset1(IndexWidth, 0), Offset2(IndexWidth, 0);
    Ptr1 = Ptr1->stripAndAccumulateInBoundsConstantOffsets(*DL, Offset1);
    Ptr2 = Ptr2->stripAndAccumulateInBoundsConstantOffsets(*DL, Offset2);
    if (Ptr1 == Ptr2) {
      // Assume WLOG that Ptr1 < Ptr2
      if (Offset1.sgt(Offset2)) {
        std::swap(Offset1, Offset2);
        std::swap(Ty1, Ty2);
      }
      bool Overflows;
      APInt Size1(IndexWidth, DL->getTypeStoreSize(Ty1));
      bool Overlaps = Offset1.sadd_ov(Size1, Overflows).sle(Offset2);
      if (!Overlaps && !Overflows)
        return false;
    }
  }

  MemoryLocation Loc2 = getLocation(Inst2, AA);
  bool Aliased = true;
  if (Loc1.Ptr && Loc2.Ptr && isSimple(Inst1) && isSimple(Inst2)) {
    // Do the alias check.
    Aliased = AA->alias(Loc1, Loc2);
  }
  if (Aliased)
    errs() << *Inst1 << ", " << *Inst2 << " may alias\n";
  return Aliased;
}

LocalDependenceAnalysis::LocalDependenceAnalysis(llvm::AliasAnalysis *AA,
                                                 const DataLayout *DL,
                                                 llvm::BasicBlock *BB,
                                                 VectorPackContext *VPCtx)
    : BB(BB), VPCtx(VPCtx) {
  std::vector<Instruction *> MemRefs;
  // Build the local dependence graph
  for (Instruction &I : *BB) {
    // PHINodes do not introduce any local dependence
    if (isa<PHINode>(&I))
      continue;

    for (Value *Operand : I.operands())
      if (auto *I2 = dyn_cast<Instruction>(Operand))
        if (!isa<PHINode>(I2) && I2->getParent() == BB)
          Dependencies[&I].push_back(I2);

    if (I.mayReadOrWriteMemory()) {
      MemoryLocation Loc = getLocation(&I, AA);
      // check dependence with preceding loads and stores
      for (auto *PrevRef : MemRefs) {
        if ((PrevRef->mayWriteToMemory() || I.mayWriteToMemory()) &&
            isAliased(Loc, &I, PrevRef, AA, DL))
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
      Depended |= TransitiveClosure[Src];
    }

    TransitiveClosure[&I] = Depended;
  }

  // Additionally, compute all independent pairs of instructions
  for (auto I = BB->begin(), E = BB->end(); I != E; ++I) {
    unsigned i = VPCtx->getScalarId(&*I);
    BitVector Independent(VPCtx->getNumValues());
    for (auto J = std::next(I); J != E; ++J) {
      if (getDepended(&*J).test(i))
        continue;
      Independent.set(VPCtx->getScalarId(&*J));
    }
    IndependentInsts[&*I] = std::move(Independent);
  }
}
