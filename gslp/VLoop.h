#ifndef VLOOP_H
#define VLOOP_H

#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/EquivalenceClasses.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"

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
class VLoopInfo {
  llvm::DenseMap<llvm::Loop *, VLoop *> LoopToVLoopMap;
  // Loops that we can't fuse because of non-identical trip count
  llvm::EquivalenceClasses<VLoop *> CoIteratingLoops;

public:
  void coiterate(VLoop *, VLoop *);
  VLoop *getVLoop(llvm::Loop *) const;
  void setVLoop(llvm::Loop *, VLoop *);
  void fuse(VLoop *, VLoop *);

  auto getCoIteratingLoops(VLoop *VL) {
    auto It = CoIteratingLoops.findValue(VL);
    assert(It != CoIteratingLoops.end());
    return llvm::make_range(CoIteratingLoops.member_begin(It),
                            CoIteratingLoops.member_end());
  }

  auto getCoIteratingLeader(VLoop *VL) {
    return CoIteratingLoops.getLeaderValue(VL);
  }
};

// This represents the eta nodes in Gated SSA
struct EtaNode {
  llvm::Value *Init;
  llvm::Value *Iter;
  EtaNode(llvm::Value *Init, llvm::Value *Iter) : Init(Init), Iter(Iter) {}
};

class VLoop {
  friend class VLoopInfo;
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
  llvm::SmallPtrSet<llvm::Instruction *, 4> LiveOuts;

  llvm::Value *ContCond;
  bool ContIfTrue; // indicate how ContCond is used

  // Condition for breaking from the loop (not including failing ContCond)
  const ControlCondition *BreakCond;

  const ControlCondition *LoopCond;

  VLoop *Parent;
  llvm::Loop *L; // the original loop

  VLoop(llvm::LoopInfo &, llvm::Loop *, VectorPackContext *,
        GlobalDependenceAnalysis &, ControlDependenceAnalysis &, VLoopInfo &);

public:
  VLoop(llvm::LoopInfo &, VectorPackContext *, GlobalDependenceAnalysis &,
        ControlDependenceAnalysis &, VLoopInfo &);

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

  static bool isSafeToCoIterate(const VLoop *, const VLoop *);

  bool haveIdenticalTripCounts(VLoop *, llvm::ScalarEvolution &);
};

bool haveIdenticalTripCounts(const llvm::Loop *, const llvm::Loop *,
                             llvm::ScalarEvolution &);

#endif
