#ifndef UNROLL_H
#define UNROLL_H

#include "llvm/ADT/DenseMap.h"
#include "llvm/IR/ValueHandle.h"
#include "llvm/Transforms/Utils/UnrollLoop.h"

struct UnrolledValue {
  unsigned Iter;
  llvm::WeakTrackingVH VH;
};

// Our version of llvm::UnrollLoop that additionally keeps track of
llvm::LoopUnrollResult UnrollLoopWithVMap(
    llvm::Loop *, llvm::UnrollLoopOptions, llvm::LoopInfo *,
    llvm::ScalarEvolution *, llvm::DominatorTree *, llvm::AssumptionCache *,
    const llvm::TargetTransformInfo *, bool PreserveLCSSA,
    llvm::DenseMap<llvm::Value *, UnrolledValue> &, llvm::Loop **);
#endif // UNROLL_H
