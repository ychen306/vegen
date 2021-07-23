#ifndef LOOP_FUSION_H
#define LOOP_FUSION_H

namespace llvm {
class ScalarEvolution;
class DependenceInfo;
class DominatorTree;
class PostDominatorTree;
class Loop;
} // namespace llvm

bool isUnsafeToFuse(llvm::Loop &, llvm::Loop &, llvm::ScalarEvolution &,
                    llvm::DependenceInfo &, llvm::DominatorTree &, llvm::PostDominatorTree &);
bool fuseLoops(llvm::Loop &, llvm::Loop &, llvm::DominatorTree &,
               llvm::PostDominatorTree &, llvm::DependenceInfo &);

#endif //  LOOP_FUSION_H
