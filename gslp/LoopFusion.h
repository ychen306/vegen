#ifndef LOOP_FUSION_H
#define LOOP_FUSION_H

namespace llvm {
class ScalarEvolution;
class DominatorTree;
class PostDominatorTree;
class Loop;
class LoopInfo;
class LazyValueInfo;
} // namespace llvm

class LazyDependenceAnalysis;
class ControlCompatibilityChecker;

bool isUnsafeToFuse(llvm::Loop *, llvm::Loop *, llvm::LoopInfo &,
                    llvm::ScalarEvolution &, LazyDependenceAnalysis &,
                    llvm::DominatorTree &, llvm::PostDominatorTree &, const ControlCompatibilityChecker *Checker=nullptr);
llvm::Loop *fuseLoops(llvm::Loop *, llvm::Loop *, llvm::LoopInfo &,
                      llvm::DominatorTree &, llvm::PostDominatorTree &,
                      llvm::ScalarEvolution &, LazyDependenceAnalysis &);

#endif //  LOOP_FUSION_H
