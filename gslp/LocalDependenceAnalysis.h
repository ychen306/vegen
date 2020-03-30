#ifndef LOCAL_DEPENDENCE_ANALYSIS_H
#define LOCAL_DEPENDENCE_ANALYSIS_H
#include "LocalDependenceAnalysis.h"
#include "VectorPackContext.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/IR/Function.h"

// Utility class to track dependency within a basic block
class LocalDependenceAnalysis {
  llvm::BasicBlock *BB;
  // mapping inst -> <users>
  llvm::DenseMap<llvm::Instruction *, std::vector<llvm::Instruction *>>
      Dependencies;
  VectorPackContext *VPCtx;
  // mapping an instruction -> instructions that it transitively depends on
  llvm::DenseMap<llvm::Instruction *, llvm::BitVector> TransitiveClosure;

public:
  LocalDependenceAnalysis(llvm::AliasAnalysis *AA, llvm::BasicBlock *BB,
                          VectorPackContext *VPCtx);

  const llvm::BitVector &getDepended(llvm::Instruction *I) const {
    auto It = TransitiveClosure.find(I);
    assert(It != TransitiveClosure.end());
    return It->second;
  }
};

#endif // end LOCAL_DEPENDENCE_ANALYSIS_H
