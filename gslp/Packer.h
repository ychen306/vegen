#ifndef PACKER_H
#define PACKER_H

#include "InstSema.h"
#include "LocalDependenceAnalysis.h"
#include "MatchManager.h"
#include "Util.h"
#include "VectorPackContext.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/IR/Function.h"
#include "llvm/InitializePasses.h"

namespace llvm {
class ScalarEvolution;
class TargetTransformInfo;
} // namespace llvm

class Packer {
  llvm::Function *F;

  // FIXME: fuse all of these together into a single map
  llvm::DenseMap<llvm::BasicBlock *, std::unique_ptr<MatchManager>> MMs;
  llvm::DenseMap<llvm::BasicBlock *, std::unique_ptr<LocalDependenceAnalysis>>
      LDAs;
  llvm::DenseMap<llvm::BasicBlock *, std::unique_ptr<ConsecutiveAccessDAG>>
      LoadDAGs;
  llvm::DenseMap<llvm::BasicBlock *, std::unique_ptr<ConsecutiveAccessDAG>>
      StoreDAGs;
  llvm::DenseMap<llvm::BasicBlock *, std::unique_ptr<VectorPackContext>> VPCtxs;

  std::vector<InstBinding *> SupportedInsts;

  llvm::TargetTransformInfo *TTI;
  llvm::BlockFrequencyInfo *BFI;

public:
  Packer(llvm::ArrayRef<InstBinding *> SupportedInsts, llvm::Function &F,
         llvm::AliasAnalysis *AA, const llvm::DataLayout *DL,
         llvm::ScalarEvolution *SE, llvm::TargetTransformInfo *TTI,
         llvm::BlockFrequencyInfo *BFI);

  VectorPackContext *getContext(llvm::BasicBlock *BB) const {
    auto It = VPCtxs.find(BB);
    assert(It != VPCtxs.end());
    return It->second.get();
  }

  llvm::ArrayRef<InstBinding *> getInsts() const { return SupportedInsts; }

  MatchManager &getMatchManager(llvm::BasicBlock *BB) { return *MMs[BB]; }
  ConsecutiveAccessDAG &getLoadDAG(llvm::BasicBlock *BB) {
    return *LoadDAGs[BB];
  }
  ConsecutiveAccessDAG &getStoreDAG(llvm::BasicBlock *BB) {
    return *StoreDAGs[BB];
  }
  LocalDependenceAnalysis &getLDA(llvm::BasicBlock *BB) { return *LDAs[BB]; }
  llvm::TargetTransformInfo *getTTI() const { return TTI; }

  llvm::Function *getFunction() const { return F; }
};

// Check if `I` is independent from things in `Elements`, which depends on
// `Depended`.
static inline bool checkIndependence(const LocalDependenceAnalysis &LDA,
                                     const VectorPackContext &VPCtx,
                                     llvm::Instruction *I,
                                     const llvm::BitVector &Elements,
                                     const llvm::BitVector &Depended) {
  unsigned Id = VPCtx.getScalarId(I);
  return !Elements.test(Id) && !Depended.test(Id) &&
         !Elements.anyCommon(LDA.getDepended(I));
}

#endif // PACKER
