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

// Auxiliary class to assign linear numbers to loads/stores
// accessing the same object (but at different offsets).
class AccessLayoutInfo {
public:
  struct AddressInfo {
    llvm::Instruction *Leader;
    unsigned Id; // Leader's id should be 0.
  };

private:
  llvm::DenseMap<llvm::Instruction *, AddressInfo> Info;
  llvm::DenseMap<llvm::Instruction *, unsigned> MemberCounts;

public:
  AccessLayoutInfo(const ConsecutiveAccessDAG &AccessDAG);
  // Get num followers + 1
  unsigned getNumMembers(llvm::Instruction *I) const {
    return MemberCounts.lookup(I);
  }

  AddressInfo get(llvm::Instruction *I) const {
    auto It = Info.find(I);
    if (It != Info.end())
      return It->second;
    return AddressInfo{I, 0};
  }

  bool isAdjacent(llvm::Instruction *I1, llvm::Instruction *I2) const {
    auto It1 = Info.find(I1);
    auto It2 = Info.find(I2);
    if (It1 == Info.end() || It2 == Info.end())
      return false;
    const AddressInfo &Info1 = It1->second;
    const AddressInfo &Info2 = It2->second;
    return Info1.Leader == Info2.Leader &&
           (Info1.Id + 1 == Info2.Id /*|| Info1.Id == Info2.Id + 1*/);
  }
};

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

  llvm::DenseMap<llvm::BasicBlock *, std::unique_ptr<AccessLayoutInfo>>
      LoadInfo;
  llvm::DenseMap<llvm::BasicBlock *, std::unique_ptr<AccessLayoutInfo>>
      StoreInfo;
  llvm::DenseMap<const OperandPack *, OperandProducerInfo> Producers;

  std::vector<InstBinding *> SupportedInsts;

  llvm::TargetTransformInfo *TTI;
  llvm::BlockFrequencyInfo *BFI;
  const llvm::DataLayout *DL;

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
  AccessLayoutInfo &getLoadInfo(llvm::BasicBlock *BB) { return *LoadInfo[BB]; }
  AccessLayoutInfo &getStoreInfo(llvm::BasicBlock *BB) { return *StoreInfo[BB]; }
  LocalDependenceAnalysis &getLDA(llvm::BasicBlock *BB) { return *LDAs[BB]; }
  llvm::TargetTransformInfo *getTTI() const { return TTI; }
  llvm::BlockFrequencyInfo *getBFI() const { return BFI; }
  const llvm::DataLayout *getDataLayout() const { return DL; }

  llvm::Function *getFunction() const { return F; }
  const OperandProducerInfo &getProducerInfo(const VectorPackContext *,
                                             const OperandPack *);
  float getScalarCost(llvm::Instruction *);
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
