#ifndef CODE_MOTION_UTIL_H
#define CODE_MOTION_UTIL_H

#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/EquivalenceClasses.h"
#include "llvm/Analysis/LoopInfo.h"

namespace llvm {
class Instruction;
class BasicBlock;
class Function;
class DominatorTree;
class PostDominatorTree;
class ScalarEvolution;
template <typename T> class SmallPtrSetImpl;
} // namespace llvm

class LazyDependenceAnalysis;
class GlobalDependenceAnalysis;
class VectorPackContext;

class ControlCompatibilityChecker {
  llvm::LoopInfo &LI;
  llvm::DominatorTree &DT;
  llvm::PostDominatorTree &PDT;
  LazyDependenceAnalysis &LDA;
  llvm::ScalarEvolution *SE;

  // Alternative to lazy DA
  VectorPackContext *VPCtx;
  GlobalDependenceAnalysis *DA;

  mutable llvm::DenseMap<std::pair<llvm::Instruction *, llvm::BasicBlock *>,
                         bool>
      Memo;

  mutable llvm::DenseMap<std::pair<llvm::Loop *, llvm::Loop *>, bool> FusionMemo;
  bool isUnsafeToFuse(llvm::Loop *, llvm::Loop *) const;
public:
  ControlCompatibilityChecker(llvm::LoopInfo &LI, llvm::DominatorTree &DT,
                              llvm::PostDominatorTree &PDT,
                              LazyDependenceAnalysis &LDA,
                              llvm::ScalarEvolution *SE,
                              VectorPackContext *VPCtx = nullptr,
                              GlobalDependenceAnalysis *DA = nullptr)
      : LI(LI), DT(DT), PDT(PDT), LDA(LDA), SE(SE), VPCtx(VPCtx), DA(DA) {}

  bool isControlCompatible(llvm::Instruction *, llvm::BasicBlock *) const;
  llvm::BasicBlock *findCompatiblePredecessorsFor(llvm::Instruction *,
                                                  llvm::BasicBlock *,
                                                  bool Inclusive) const;
};

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
void hoistTo(
    llvm::Instruction *, llvm::BasicBlock *, llvm::LoopInfo &,
    llvm::ScalarEvolution &, llvm::DominatorTree &, llvm::PostDominatorTree &,
    LazyDependenceAnalysis &,
    const llvm::EquivalenceClasses<llvm::Instruction *> &CoupledInsts = {});

// Determine if it's possible move an instruction into another basic block
bool isControlCompatible(llvm::Instruction *, llvm::BasicBlock *,
                         llvm::LoopInfo &, llvm::DominatorTree &,
                         llvm::PostDominatorTree &, LazyDependenceAnalysis &,
                         llvm::ScalarEvolution *);

bool isControlCompatible(llvm::Instruction *, llvm::Instruction *,
                         llvm::LoopInfo &, llvm::DominatorTree &,
                         llvm::PostDominatorTree &, LazyDependenceAnalysis &,
                         llvm::ScalarEvolution *);

// Find a dominator for BB that's also control-compatible for I
llvm::BasicBlock *findCompatiblePredecessorsFor(
    llvm::Instruction *I, llvm::BasicBlock *BB, llvm::LoopInfo &,
    llvm::DominatorTree &, llvm::PostDominatorTree &, LazyDependenceAnalysis &,
    llvm::ScalarEvolution *, bool Inclusive = true);

// If want to include dependences found in Earliest, set Inclusive=true
void findDependences(llvm::Instruction *I, llvm::BasicBlock *Earliest,
                     llvm::LoopInfo &LI, llvm::DominatorTree &DT,
                     LazyDependenceAnalysis &LDA,
                     llvm::SmallPtrSetImpl<llvm::Instruction *> &Depended,
                     bool Inclusive = false);

bool comesBefore(llvm::BasicBlock *, llvm::BasicBlock *, llvm::Loop *);

void fixDefUseDominance(llvm::Function *, llvm::DominatorTree &);

class GlobalDependenceAnalysis;
class VectorPackContext;

// Move code around so that instructions in the same equivalence class end up in
// the same basic block
void gatherInstructions(llvm::Function *,
                        const llvm::EquivalenceClasses<llvm::Instruction *> &,
                        llvm::LoopInfo &, llvm::DominatorTree &,
                        llvm::PostDominatorTree &, llvm::ScalarEvolution &,
                        LazyDependenceAnalysis &,
                        GlobalDependenceAnalysis *DA = nullptr,
                        const VectorPackContext *VPCtx = nullptr);

bool haveIdenticalTripCounts(const llvm::Loop *, const llvm::Loop *,
                             llvm::ScalarEvolution &);

#endif // CODE_MOTION_UTIL_H
