#ifndef PACKER_H
#define PACKER_H

#include "IRModel.h"
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

// Do a quadratic search to build the access dags
template <typename MemAccessTy>
void buildAccessDAG(ConsecutiveAccessDAG &DAG,
                    llvm::ArrayRef<MemAccessTy *> Accesses,
                    const llvm::DataLayout *DL, llvm::ScalarEvolution *SE) {
  using namespace llvm;
  for (auto *A1 : Accesses) {
    // Get type of the value being acccessed
    auto *Ty =
        cast<PointerType>(A1->getPointerOperand()->getType())->getElementType();
    if (!isScalarType(Ty))
      continue;
    for (auto *A2 : Accesses) {
      if (A1->getType() == A2->getType() &&
          isConsecutiveAccess(A1, A2, *DL, *SE))
        DAG[A1].insert(A2);
    }
  }
};

// FIXME: remove Insts and take the list of all supported instruction instead
// FIXME: ignore lane order here.
// Find vector packs that produces operand pack
void extendWithDef(
    const VectorPack::OperandPack &OpndPack, const VectorPackSet &ExistingPacks,
    std::vector<VectorPack *> &Extensions,
    llvm::DenseMap<llvm::BasicBlock *, std::unique_ptr<ConsecutiveAccessDAG>>
        &LoadDAGs,
    llvm::DenseMap<llvm::BasicBlock *, std::unique_ptr<MatchManager>> &MMs,
    llvm::DenseMap<llvm::BasicBlock *, std::unique_ptr<VectorPackContext>>
        &VPCtxs,
    llvm::DenseMap<llvm::BasicBlock *, std::unique_ptr<LocalDependenceAnalysis>>
        &LDAs,
    llvm::DenseMap<llvm::BasicBlock *,
                   llvm::SmallPtrSet<const InstBinding *, 4>> &Insts,
    llvm::TargetTransformInfo *TTI);

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
  IRIndex Index;

  // First find out if which vector instruction we can emit.
  // E.g. sometimes there is simply no `fadd` in a basic block..
  llvm::DenseMap<llvm::BasicBlock *, llvm::SmallPtrSet<const InstBinding *, 4>>
      InstBindings;

public:
  Packer(llvm::ArrayRef<InstBinding *> SupportedInsts, llvm::Function &F,
         llvm::AliasAnalysis *AA, const llvm::DataLayout *DL,
         llvm::ScalarEvolution *SE, llvm::TargetTransformInfo *TTI,
         llvm::BlockFrequencyInfo *BFI);

  void findExtensionForOnePack(const VectorPack &VP, const VectorPackSet &Packs,
                               std::vector<VectorPack *> &Extensions);

  float evalSeedPacks(const VectorPackSet &Packs, unsigned Alpha = 4);

  PackSample samplePackForInst(llvm::Instruction *I,
                               VectorPackSet &ExistingPacks,
                               PackDistribution &PackDistr) {
    return PackDistr.sample(Index, I, ExistingPacks, SupportedInsts, LDAs,
                            LoadDAGs, StoreDAGs, VPCtxs, MMs, TTI);
  }

  PackDistribution runModel(PackModel &Model) {
    return Model->forward(Index, LoadDAGs, StoreDAGs);
  }

  llvm::Function *getFunction() const { return F; }
};

#endif // PACKER
