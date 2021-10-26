#ifndef PACKER_H
#define PACKER_H

#include "ControlDependence.h"
#include "DependenceAnalysis.h"
#include "InstSema.h"
#include "MatchManager.h"
#include "VectorPackContext.h"
#include "VLoop.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/Analysis/VectorUtils.h"
#include "llvm/IR/Function.h"

namespace llvm {
class ScalarEvolution;
class DependenceInfo;
class DominatorTree;
class PostDominatorTree;
class TargetTransformInfo;
class LoopInfo;
} // namespace llvm

using ConsecutiveAccessDAG =
    llvm::DenseMap<llvm::Instruction *,
                   llvm::SmallPtrSet<llvm::Instruction *, 4>>;

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
  AccessLayoutInfo() = default;
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

// Util class to remember the RPO of the basic blocks within a function
class BlockOrdering {
  // This marks the basic blocks in RPO
  llvm::DenseMap<llvm::BasicBlock *, unsigned> Order;

public:
  BlockOrdering(llvm::Function *F);
  bool comesBefore(llvm::BasicBlock *, llvm::BasicBlock *) const;
  bool comesBefore(llvm::Instruction *, llvm::Instruction *) const;
};

class Packer {
  llvm::Function *F;
  VectorPackContext VPCtx;
  GlobalDependenceAnalysis DA;
  ControlDependenceAnalysis CDA;
  VLoopInfo VLI;
  VLoop TopVL;

  MatchManager MM;
  BlockOrdering BO;

  llvm::ScalarEvolution *SE;
  llvm::DominatorTree *DT;
  llvm::PostDominatorTree *PDT;
  llvm::LoopInfo *LI;

  ConsecutiveAccessDAG LoadDAG, StoreDAG;
  AccessLayoutInfo LoadInfo, StoreInfo;
  llvm::DenseMap<const OperandPack *, OperandProducerInfo> Producers;

  llvm::DenseMap<llvm::BasicBlock *, const ControlCondition *> BlockConditions;
  llvm::DenseMap<std::pair<llvm::BasicBlock *, llvm::BasicBlock *>,
                 const ControlCondition *>
      EdgeConditions;

  std::vector<const InstBinding *> SupportedInsts;

  llvm::LazyValueInfo *LVI;
  llvm::TargetTransformInfo *TTI;
  llvm::BlockFrequencyInfo *BFI;

public:
  Packer(llvm::ArrayRef<const InstBinding *> SupportedInsts, llvm::Function &F,
         llvm::AliasAnalysis *AA, llvm::LoopInfo *LI, llvm::ScalarEvolution *SE,
         llvm::DominatorTree *DT, llvm::PostDominatorTree *PDT,
         llvm::DependenceInfo *DI, llvm::LazyValueInfo *LVI,
         llvm::TargetTransformInfo *TTI, llvm::BlockFrequencyInfo *BFI,
         llvm::EquivalenceClasses<llvm::BasicBlock *> *UnrolledBlocks = nullptr,
         bool Preplanning = false);

  const VectorPackContext *getContext() const { return &VPCtx; }

  llvm::ArrayRef<const InstBinding *> getInsts() const {
    return SupportedInsts;
  }

  MatchManager &getMatchManager() { return MM; }
  ConsecutiveAccessDAG &getLoadDAG() { return LoadDAG; }
  ConsecutiveAccessDAG &getStoreDAG() { return StoreDAG; }
  AccessLayoutInfo &getLoadInfo() { return LoadInfo; }
  AccessLayoutInfo &getStoreInfo() { return StoreInfo; }
  GlobalDependenceAnalysis &getDA() { return DA; }
  llvm::TargetTransformInfo *getTTI() const { return TTI; }
  llvm::BlockFrequencyInfo *getBFI() const { return BFI; }

  llvm::ScalarEvolution &getSE() const { return *SE; }
  llvm::DominatorTree &getDT() const { return *DT; }
  llvm::PostDominatorTree &getPDT() const { return *PDT; }
  llvm::LoopInfo &getLoopInfo() const { return *LI; }
  VLoopInfo &getVLoopInfo() { return VLI; }
  llvm::LazyValueInfo &getLVI() const { return *LVI; }

  const llvm::DataLayout *getDataLayout() const {
    return &F->getParent()->getDataLayout();
  }

  const ControlCondition *getBlockCondition(llvm::BasicBlock *BB) const {
    return BlockConditions.lookup(BB);
  }
  const ControlCondition *getEdgeCondition(llvm::BasicBlock *Src,
                                           llvm::BasicBlock *Dst) const {
    return EdgeConditions.lookup({Src, Dst});
  }
  // Get the condition pack guarding a list of instructions
  template <typename InstContainer>
  const ConditionPack *getConditionPack(const InstContainer &Insts) const {
    llvm::SmallVector<const ControlCondition *> Conds;
    auto *SomeInst = *llvm::find_if(Insts, [](auto *Inst) { return Inst; });
    auto *C = getBlockCondition(SomeInst->getParent());
    for (auto *I : Insts)
      Conds.push_back(I ? getBlockCondition(I->getParent()) : C);
    return VPCtx.getConditionPack(Conds);
  }

  llvm::Function *getFunction() const { return F; }
  const OperandProducerInfo &getProducerInfo(const OperandPack *);
  float getScalarCost(llvm::Instruction *);
  bool isCompatible(llvm::Instruction *, llvm::Instruction *);
  VLoop *getVLoopFor(llvm::Instruction *);
  VLoop &getTopVLoop() { return TopVL; }
  void fuseOrCoIterateLoops(VLoop *, VLoop *);
  bool canSpeculateAt(llvm::Value *V, const ControlCondition *C);
};

// Check if `I` is independent from things in `Elements`, which depends on
// `Depended`.
static inline bool checkIndependence(const GlobalDependenceAnalysis &DA,
                                     const VectorPackContext &VPCtx,
                                     llvm::Instruction *I,
                                     const llvm::BitVector &Elements,
                                     const llvm::BitVector &Depended) {
  unsigned Id = VPCtx.getScalarId(I);
  return !Elements.test(Id) && !Depended.test(Id) &&
         !Elements.anyCommon(DA.getDepended(I));
}

unsigned getBitWidth(llvm::Value *V, const llvm::DataLayout *);

#endif // PACKER
