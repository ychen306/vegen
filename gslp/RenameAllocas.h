#ifndef RENAME_ALLOCAS_H
#define RENAME_ALLOCAS_H

#include "llvm/ADT/ArrayRef.h"

namespace llvm {
class AllocaInst;
class DominatorTree;
class PostDominatorTree;
} // namespace llvm

// Find disjoint lifetimes for a given alloca, and assign a new alloca for each
// lifetime (and replace the use of the old alloca with the new one)
void renameAllocas(llvm::DominatorTree &, llvm::PostDominatorTree &,
                   llvm::ArrayRef<llvm::AllocaInst *>);

#endif // RENAME_ALLOCAS_H
