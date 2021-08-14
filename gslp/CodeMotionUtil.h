#ifndef CODE_MOTION_UTIL_H
#define CODE_MOTION_UTIL_H

#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/Analysis/LoopInfo.h"

namespace llvm {
class Instruction;
class BasicBlock;
class DominatorTree;
class DependenceInfo;
template <typename T> class EquivalenceClasses;
template <typename T> class SmallPtrSetImpl;
} // namespace llvm

// Use this to do DFS without taking the backedge
struct SkipBackEdge : public llvm::df_iterator_default_set<llvm::BasicBlock *> {
  SkipBackEdge(llvm::Loop *L) {
    if (L) {
      assert(L->getLoopLatch());
      insert(L->getLoopLatch());
    }
  }
};

void getInBetweenInstructions(
    llvm::Instruction *I, llvm::BasicBlock *Earliest, llvm::Loop *ParentLoop,
    llvm::SmallPtrSetImpl<llvm::Instruction *> &InBetweenInsts);

// Hoist an instruction to the end of a basic block.
// `CoupledInsts` are equivalent classes of instructions that should always
// be in the same basic block.
void hoistTo(llvm::Instruction *, llvm::BasicBlock *, llvm::Loop *ParentLoop,
             llvm::DominatorTree &, llvm::DependenceInfo &,
             const llvm::EquivalenceClasses<llvm::Instruction *> &CoupledInsts);

void findDependencies(llvm::Instruction *I, llvm::BasicBlock *Earliest,
                      llvm::Loop *ParentLoop, llvm::DominatorTree &DT,
                      llvm::DependenceInfo &DI,
                      llvm::SmallPtrSetImpl<llvm::Instruction *> &Depended);

#endif // CODE_MOTION_UTIL_H
