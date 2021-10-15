#ifndef VLOOP_H
#define VLOOP_H

#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/SmallVector.h"

namespace llvm {
class Loop;
class Instruction;
class Value;
class LoopInfo;
class ScalarEvolution;
} // namespace llvm

class VectorPackContext;
class GlobalDependenceAnalysis;

class VLoop {
  // Instructions that this loop dependes on (and not in the loop)
  llvm::BitVector Depended;
  // All instructions included in the loop (including those in the subloops)
  llvm::BitVector Insts;
  llvm::SmallVector<llvm::Instruction *> TopLevelInsts;
  llvm::SmallVector<std::unique_ptr<VLoop>, 4> SubLoops;

  llvm::Value *LoopCond;
  bool LoopIfTrue; // indicate how LoopCond is used

  VLoop *Parent;
  llvm::Loop *L; // the original loop

public:
  VLoop(llvm::LoopInfo &, llvm::Loop *L, VectorPackContext *VPCtx, GlobalDependenceAnalysis *DA);
  llvm::ArrayRef<llvm::Instruction *> getInstructions() const { return TopLevelInsts; }
  llvm::ArrayRef<std::unique_ptr<VLoop>> getSubLoops() const { return SubLoops; }
  const llvm::BitVector &getDepended() const { return Depended; }

  static bool isSafeToFuse(const VLoop *, const VLoop *, llvm::ScalarEvolution &);
  static void fuse(VLoop *, VLoop *);
};

#endif
