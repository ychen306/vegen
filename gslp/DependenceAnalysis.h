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
class Function;
} // namespace llvm

class VectorPackContext;

// Utility class to track dependency within a function
class GlobalDependenceAnalysis {
  // Mapping an instruction -> instructions that it transitively depends on
  llvm::DenseMap<llvm::Instruction *, llvm::BitVector> TransitiveClosure;
  // Mapp an instruction -> instructions that are indepenpendent
  llvm::DenseMap<llvm::Instruction *, llvm::BitVector> IndependentInsts;

public:
  GlobalDependenceAnalysis(llvm::AliasAnalysis &,
                          llvm::ScalarEvolution &,
                          llvm::DominatorTree &,
                          llvm::Function *,
                          llvm::LazyValueInfo *, VectorPackContext *);

  const llvm::BitVector &getDepended(llvm::Instruction *I) const {
    auto It = TransitiveClosure.find(I);
    assert(It != TransitiveClosure.end());
    return It->second;
  }
};

#endif // DEPENDENCE_ANALYSIS_H
