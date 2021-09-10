#ifndef UNROLL_FACTOR_H
#define UNROLL_FACTOR_H

#include "llvm/ADT/DenseMap.h"

namespace llvm {
class Function;
class Loop;
class LoopInfo;
} // namespace llvm

// Compute the the unroll factors
// for all loop-nests in F that best benefit vectorization
void computeUnrollFactor(const llvm::Function *F, const llvm::LoopInfo &LI,
                         llvm::DenseMap<const llvm::Loop *, unsigned> &UFs);

#endif // UNROLL_FACTOR_H
