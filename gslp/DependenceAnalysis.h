#ifndef DEPENDENCE_ANALYSIS_H
#define DEPENDENCE_ANALYSIS_H

namespace llvm {
class DependenceInfo;
class LazyValueInfo;
class ScalarEvolution;
class DominatorTree;
class Instruction;
} // namespace llvm

bool depends(llvm::Instruction *Def, llvm::Instruction *Use,
             llvm::DependenceInfo &, llvm::ScalarEvolution &,
             llvm::DominatorTree &DT, llvm::LazyValueInfo *LVI = nullptr);

#endif // DEPENDENCE_ANALYSIS_H
