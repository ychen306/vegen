#ifndef UNROLL_FACTOR_H
#define UNROLL_FACTOR_H

#include "llvm/ADT/DenseMap.h"

namespace llvm {
class BasicBlock;
class Function;
class Loop;
class LoopInfo;
class ScalarEvolution;
class AssumptionCache;
class DominatorTree;
class TargetTransformInfo;
class LazyValueInfo;
class BlockFrequencyInfo;
} // namespace llvm

class InstBinding;

// Mapping duplicated (inner) loops to the original loops
struct UnrolledLoopTy {
  llvm::Loop *OrigLoop;
  unsigned Iter;
  UnrolledLoopTy() = default;
  UnrolledLoopTy(llvm::Loop *L, unsigned I) : OrigLoop(L), Iter(I) {}
};

// Compute the the unroll factors
// for all loop-nests in F that best benefit vectorization
void computeUnrollFactor(llvm::ArrayRef<const InstBinding *> Insts,
                         llvm::LazyValueInfo *LVI,
                         llvm::TargetTransformInfo *TTI,
                         llvm::BlockFrequencyInfo *BFI,
                         llvm::Function *F, const llvm::LoopInfo &LI,
                         llvm::DenseMap<llvm::Loop *, unsigned> &UFs);

void unrollLoops(
    llvm::Function *F, llvm::ScalarEvolution &SE, llvm::LoopInfo &LI,
    llvm::AssumptionCache &AC, llvm::DominatorTree &DT,
    llvm::TargetTransformInfo *TTI,
    const llvm::DenseMap<llvm::Loop *, unsigned> &UFs,
    llvm::DenseMap<llvm::Loop *, UnrolledLoopTy> &DupToOrigLoopMap,
    llvm::DenseMap<llvm::BasicBlock *, unsigned> *UnrolledIterations = nullptr);

#endif // UNROLL_FACTOR_H
