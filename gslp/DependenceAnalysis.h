#ifndef DEPENDENCE_ANALYSIS_H
#define DEPENDENCE_ANALYSIS_H

#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Analysis/AliasAnalysis.h"

namespace llvm {
class LazyValueInfo;
class ScalarEvolution;
class DominatorTree;
class Instruction;
class DependenceInfo;
class LoopInfo;
class Function;
} // namespace llvm

class VectorPackContext;

// Utility class to track dependency within a function
class GlobalDependenceAnalysis {
  VectorPackContext *VPCtx;
  // Mapping an instruction -> instructions that it transitively depends on
  llvm::DenseMap<llvm::Instruction *, llvm::BitVector> TransitiveClosure;

public:
  GlobalDependenceAnalysis(llvm::AliasAnalysis &, llvm::ScalarEvolution &,
                           llvm::DominatorTree &, llvm::LoopInfo &LI,
                           llvm::LazyValueInfo &, llvm::Function *,
                           VectorPackContext *, bool NoAlias);

  const llvm::BitVector &getDepended(llvm::Instruction *I) const {
    auto It = TransitiveClosure.find(I);
    assert(It != TransitiveClosure.end());
    return It->second;
  }

  void addDependences(llvm::Instruction *, llvm::ArrayRef<llvm::Instruction *> Deps);
};

#endif // DEPENDENCE_ANALYSIS_H
