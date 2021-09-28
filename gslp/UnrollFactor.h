#ifndef UNROLL_FACTOR_H
#define UNROLL_FACTOR_H

#include "LoopUnrolling.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"

namespace llvm {
class Instruction;
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
template <typename T> class EquivalenceClasses;
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

struct UnrolledInstruction {
  const llvm::Instruction *OrigI;
  unsigned Iter;
};

// UnrolledBlocks track the set of blocks unrolled from the same original block
void unrollLoops(
    llvm::Function *F, llvm::ScalarEvolution &SE, llvm::LoopInfo &LI,
    llvm::AssumptionCache &AC, llvm::DominatorTree &DT,
    llvm::TargetTransformInfo *TTI,
    const llvm::DenseMap<llvm::Loop *, unsigned> &UFs,
    llvm::DenseMap<llvm::Loop *, UnrolledLoopTy> &DupToOrigLoopMap,
    llvm::DenseMap<llvm::Instruction *, UnrolledInstruction> *UnrolledIterations = nullptr,
    llvm::DenseSet<llvm::BasicBlock *> *Epilogblocks = nullptr,
    llvm::EquivalenceClasses<llvm::BasicBlock *> *UnrolledBlocks = nullptr);

#endif // UNROLL_FACTOR_H
