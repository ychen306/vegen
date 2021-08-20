#ifndef CODE_MOTION_UTIL_H
#define CODE_MOTION_UTIL_H

#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/Analysis/LoopInfo.h"

namespace llvm {
class Instruction;
class BasicBlock;
class Function;
class DominatorTree;
class PostDominatorTree;
class DependenceInfo;
class ScalarEvolution;
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
    llvm::Instruction *I, llvm::BasicBlock *Earliest, llvm::LoopInfo *,
    llvm::SmallPtrSetImpl<llvm::Instruction *> &InBetweenInsts);

// Hoist an instruction to the end of a basic block.
// `CoupledInsts` are equivalent classes of instructions that should always
// be in the same basic block.
void hoistTo(llvm::Instruction *, llvm::BasicBlock *, llvm::LoopInfo &,
             llvm::ScalarEvolution &, llvm::DominatorTree &,
             llvm::PostDominatorTree &, llvm::DependenceInfo &,
             const llvm::EquivalenceClasses<llvm::Instruction *> &CoupledInsts);

// Determine if it's possible move an instruction into another basic block
bool isControlCompatible(llvm::Instruction *, llvm::BasicBlock *,
                         llvm::LoopInfo &, llvm::DominatorTree &,
                         llvm::PostDominatorTree &, llvm::DependenceInfo &,
                         llvm::ScalarEvolution *);

bool isControlCompatible(llvm::Instruction *, llvm::Instruction *,
                         llvm::LoopInfo &, llvm::DominatorTree &,
                         llvm::PostDominatorTree &, llvm::DependenceInfo &,
                         llvm::ScalarEvolution *);

// Find a dominator for BB that's also control-compatible for I
llvm::BasicBlock *
findCompatiblePredecessorsFor(llvm::Instruction *I, llvm::BasicBlock *BB,
                              llvm::LoopInfo &, llvm::DominatorTree &,
                              llvm::PostDominatorTree &, llvm::DependenceInfo &,
                              llvm::ScalarEvolution *, bool Inclusive = true);

// If want to include dependences found in Earliest, set Inclusive=true
void findDependences(llvm::Instruction *I, llvm::BasicBlock *Earliest,
                     llvm::LoopInfo &LI, llvm::DominatorTree &DT,
                     llvm::DependenceInfo &DI,
                     llvm::SmallPtrSetImpl<llvm::Instruction *> &Depended,
                     bool Inclusive = false);

bool comesBefore(llvm::BasicBlock *, llvm::BasicBlock *, llvm::Loop *);

void fixDefUseDominance(llvm::Function *, llvm::DominatorTree &);

// Move code around so that instructions in the same equivalence class end up in
// the same basic block
void gatherInstructions(const llvm::EquivalenceClasses<llvm::Instruction *> &,
                        llvm::LoopInfo &, llvm::DominatorTree &,
                        llvm::PostDominatorTree &, llvm::ScalarEvolution &,
                        llvm::DependenceInfo &);

#endif // CODE_MOTION_UTIL_H
