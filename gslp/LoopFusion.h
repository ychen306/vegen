#ifndef LOOP_FUSION_H
#define LOOP_FUSION_H

namespace llvm {
class ScalarEvolution;
class DependenceInfo;
class DominatorTree;
class PostDominatorTree;
class Loop;
class LoopInfo;
class LazyValueInfo;
} // namespace llvm

bool isUnsafeToFuse(llvm::Loop *, llvm::Loop *, llvm::LoopInfo &,
                    llvm::ScalarEvolution &, llvm::DependenceInfo &,
                    llvm::DominatorTree &, llvm::PostDominatorTree &);
llvm::Loop *fuseLoops(llvm::Loop *, llvm::Loop *, llvm::LoopInfo &,
                      llvm::DominatorTree &, llvm::PostDominatorTree &,
                      llvm::ScalarEvolution &, llvm::DependenceInfo &,
                      llvm::LazyValueInfo *LVI = nullptr);

#endif //  LOOP_FUSION_H
