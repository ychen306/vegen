#ifndef CONTROL_EQUIVALENCE_H
#define CONTROL_EQUIVALENCE_H
namespace llvm {
class BasicBlock;
class DominatorTree;
class PostDominatorTree;
} // namespace llvm

bool isControlEquivalent(const llvm::BasicBlock &BB0,
                         const llvm::BasicBlock &BB1,
                         const llvm::DominatorTree &,
                         const llvm::PostDominatorTree &);
#endif // CONTROL_EQUIVALENCE_H
