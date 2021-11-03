#ifndef RENAME_ALLOCAS_H
#define RENAME_ALLOCAS_H

#include "llvm/ADT/ArrayRef.h"
#include "llvm/Analysis/AliasAnalysis.h"

namespace llvm {
class AllocaInst;
class DominatorTree;
class PostDominatorTree;
class LoopInfo;
class DataLayout;
} // namespace llvm

// Find disjoint lifetimes for a given alloca, and assign a new alloca for each
// lifetime (and replace the use of the old alloca with the new one)
void renameAllocas(llvm::DominatorTree &, llvm::PostDominatorTree &,
                   llvm::LoopInfo &, llvm::AliasAnalysis &AA,
                   const llvm::DataLayout &,
                   llvm::ArrayRef<llvm::AllocaInst *>);

#endif // RENAME_ALLOCAS_H
