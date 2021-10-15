#ifndef VLOOP_H
#define VLOOP_H

#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/SmallVector.h"

namespace llvm {
class Loop;
class Instruction;
class Value;
class LoopInfo;
} // namespace llvm

class VectorPackContext;
class GlobalDependenceAnalysis;

class VLoop {
  // Instructions that this loop dependes on (and not in the loop)
  llvm::BitVector Depended;
  std::vector<llvm::Instruction *> Insts;
  llvm::SmallVector<VLoop *, 4> SubLoops;

  llvm::Value *LoopCond;
  bool LoopIfTrue; // indicate how LoopCond is used

  VLoop *Parent;

  llvm::SmallVector<std::unique_ptr<VLoop>, 4> LoopStorage;

public:
  VLoop(llvm::LoopInfo &, llvm::Loop *L, VectorPackContext *VPCtx, GlobalDependenceAnalysis *DA);
  llvm::ArrayRef<llvm::Instruction *> getInstructions() const { return Insts; }
  llvm::ArrayRef<VLoop *> getSubLoops() const { return SubLoops; }
  const llvm::BitVector &getDepended() const { return Depended; }
};

#endif
