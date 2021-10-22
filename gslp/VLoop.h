#ifndef VLOOP_H
#define VLOOP_H

#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/DenseMap.h"

namespace llvm {
class Loop;
class Instruction;
class Value;
class LoopInfo;
class ScalarEvolution;
class PHINode;
} // namespace llvm

class VectorPackContext;
class GlobalDependenceAnalysis;
class ControlDependenceAnalysis;
class ControlCondition;

class VLoop;
using LoopToVLoopMapTy = llvm::DenseMap<llvm::Loop *, VLoop *>;

// This represents the eta nodes in Gated SSA
struct EtaNode {
  llvm::Value *Init;
  llvm::Value *Iter;
  EtaNode(llvm::Value *Init, llvm::Value *Iter) : Init(Init), Iter(Iter) {}
};

class VLoop {
  bool IsTopLevel; // True if this VLoop doesn't represent any actual loop but
                   // the whole function

  // Instructions that this loop dependes on (and not in the loop)
  llvm::BitVector Depended;
  // All instructions included in the loop (including those in the subloops)
  llvm::BitVector Insts;
  llvm::SmallVector<llvm::Instruction *> TopLevelInsts;
  llvm::SmallVector<std::unique_ptr<VLoop>, 4> SubLoops;
  // Mapping phi nodes to their equivalent etas
  llvm::SmallDenseMap<llvm::PHINode *, EtaNode, 8> Etas;

  llvm::Value *ContCond;
  bool ContIfTrue; // indicate how ContCond is used

  // Condition for breaking from the loop (not including failing ContCond)
  const ControlCondition *BreakCond;

  const ControlCondition *LoopCond;

  VLoop *Parent;
  llvm::Loop *L; // the original loop

  VLoop(llvm::LoopInfo &, llvm::Loop *, VectorPackContext *,
        GlobalDependenceAnalysis &, ControlDependenceAnalysis &,
        LoopToVLoopMapTy &);

public:
  VLoop(llvm::LoopInfo &, VectorPackContext *, GlobalDependenceAnalysis &,
        ControlDependenceAnalysis &, LoopToVLoopMapTy &);

  llvm::ArrayRef<llvm::Instruction *> getInstructions() const {
    return TopLevelInsts;
  }
  llvm::ArrayRef<std::unique_ptr<VLoop>> getSubLoops() const {
    return SubLoops;
  }
  const llvm::BitVector &getDepended() const { return Depended; }
  const ControlCondition *getLoopCond() const { return LoopCond; }
  const ControlCondition *getBreakCond() const { return BreakCond; }
  bool isLoop() const { return L; }
  llvm::Optional<EtaNode> getEta(llvm::PHINode *) const;
  llvm::Value *getContinueCondition() const { return ContCond; }
  bool continueIfTrue() const { return ContIfTrue; }

  static bool isSafeToFuse(const VLoop *, const VLoop *,
                           llvm::ScalarEvolution &);
  static void fuse(VLoop *, VLoop *, LoopToVLoopMapTy &);
};

bool haveIdenticalTripCounts(const llvm::Loop *, const llvm::Loop *,
                             llvm::ScalarEvolution &);

#endif
