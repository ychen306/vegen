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

// FIXME add a wrapper pass for this
// A wrapper around dependence info that tries to be somewhat context sensitive
class LazyDependenceAnalysis {
  llvm::AliasAnalysis &AA;
  llvm::DependenceInfo &DI;
  llvm::ScalarEvolution &SE;
  llvm::DominatorTree &DT;
  llvm::LoopInfo &LI;
  llvm::LazyValueInfo &LVI;

public:
  LazyDependenceAnalysis(llvm::AliasAnalysis &AA, llvm::DependenceInfo &DI,
                         llvm::ScalarEvolution &SE, llvm::DominatorTree &DT,
                         llvm::LoopInfo &LI, llvm::LazyValueInfo &LVI)
      : AA(AA), DI(DI), SE(SE), DT(DT), LI(LI), LVI(LVI) {}
  bool depends(llvm::Instruction *I1, llvm::Instruction *I2);
};

class VectorPackContext;

// Utility class to track dependency within a function
class GlobalDependenceAnalysis {
  // Mapping an instruction -> instructions that it transitively depends on
  llvm::DenseMap<llvm::Instruction *, llvm::BitVector> TransitiveClosure;
  // Mapp an instruction -> instructions that are indepenpendent
  llvm::DenseMap<llvm::Instruction *, llvm::BitVector> IndependentInsts;

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
};

#endif // DEPENDENCE_ANALYSIS_H
