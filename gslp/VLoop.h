#ifndef VLOOP_H
#define VLOOP_H

#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
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
class AllocaInst;
class LLVMContext;
} // namespace llvm

class VectorPackContext;
class GlobalDependenceAnalysis;
class ControlDependenceAnalysis;
class ControlCondition;

class VLoop;
class VLoopInfo {
  llvm::DenseMap<llvm::Loop *, VLoop *> LoopToVLoopMap;
  llvm::DenseMap<llvm::Instruction *, VLoop *> InstToVLoopMap;
  llvm::DenseSet<VLoop *> DeletedLoops;
  // Loops that we can't fuse because of non-identical trip count
  llvm::EquivalenceClasses<VLoop *> CoIteratingLoops;

public:
  void mapInstToLoop(llvm::Instruction *I, VLoop *VL) {
    InstToVLoopMap[I] = VL;
  }
  void coiterate(VLoop *, VLoop *);
  // jam loops that we are coiterating together
  void doCoiteration(llvm::LLVMContext &, const VectorPackContext &,
                     GlobalDependenceAnalysis &, ControlDependenceAnalysis &);
  VLoop *getVLoop(llvm::Loop *) const;
  void setVLoop(llvm::Loop *, VLoop *);
  void fuse(VLoop *, VLoop *);

  VLoop *getLoopForInst(llvm::Instruction *I) const {
    assert(InstToVLoopMap.count(I));
    return InstToVLoopMap.lookup(I);
  }

  auto getCoIteratingLoops(VLoop *VL) {
    auto It = CoIteratingLoops.findValue(VL);
    assert(It != CoIteratingLoops.end());
    return llvm::make_range(CoIteratingLoops.member_begin(It),
                            CoIteratingLoops.member_end());
  }

  auto getCoIteratingLeader(VLoop *VL) {
    return CoIteratingLoops.getLeaderValue(VL);
  }

  bool isCoIterating(VLoop *VL) const;
};

// This represents the mu nodes in Gated SSA
struct MuNode {
  llvm::Value *Init;
  llvm::Value *Iter;
  MuNode(llvm::Value *Init, llvm::Value *Iter) : Init(Init), Iter(Iter) {}
};

// This represents a special kind of gated phi
struct OneHotPhi {
  const ControlCondition *C;
  llvm::Value *IfTrue;
  llvm::Value *IfFalse;
  OneHotPhi(const ControlCondition *C, llvm::Value *IfTrue,
            llvm::Value *IfFalse)
      : C(C), IfTrue(IfTrue), IfFalse(IfFalse) {}
};

class VLoop {
  VectorPackContext *VPCtx;
  VLoopInfo &VLI;
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
  llvm::SmallDenseMap<llvm::PHINode *, MuNode, 8> Mus;
  llvm::DenseMap<llvm::PHINode *, OneHotPhi> OneHotPhis;
  llvm::DenseMap<llvm::PHINode *, llvm::SmallVector<const ControlCondition *, 4>> GatedPhis;
  // Mapping instruction -> <its guarded value, i.e., the value that instructions outside of this loop should use>
  llvm::DenseMap<llvm::Instruction *, llvm::Instruction *> GuardedLiveOuts;
  llvm::DenseMap<llvm::Instruction *, const ControlCondition *> InstConds;

  // Should we execute this loop at all
  const ControlCondition *LoopCond;
  // Is the backedge taken
  const ControlCondition *BackEdgeCond;

  VLoop *Parent;
  llvm::Loop *L; // the original loop

  VLoop(llvm::LoopInfo &, llvm::Loop *, VectorPackContext *,
        GlobalDependenceAnalysis &, ControlDependenceAnalysis &, VLoopInfo &);

public:
  VLoop(llvm::LoopInfo &, VectorPackContext *, GlobalDependenceAnalysis &,
        ControlDependenceAnalysis &, VLoopInfo &);

  const decltype(GuardedLiveOuts) &getGuardedLiveOuts() const { return GuardedLiveOuts; }

  void addInstruction(llvm::Instruction *I, const ControlCondition *C);

  // Create a one-hot gated phi that's true only if the control-condition is
  // true
  llvm::Instruction *createOneHotPhi(const ControlCondition *,
                                     llvm::Value *IfTrue, llvm::Value *IfFalse);

  llvm::ArrayRef<llvm::Instruction *> getInstructions() const {
    return TopLevelInsts;
  }
  const ControlCondition *getInstCond(llvm::Instruction *I) const {
    assert(InstConds.count(I));
    return InstConds.lookup(I);
  }
  llvm::ArrayRef<std::unique_ptr<VLoop>> getSubLoops() const {
    return SubLoops;
  }
  const llvm::BitVector &getDepended() const { return Depended; }
  const ControlCondition *getLoopCond() const { return LoopCond; }
  const ControlCondition *getBackEdgeCond() const { return BackEdgeCond; }
  bool isLoop() const { return L; }
  llvm::Optional<MuNode> getMu(llvm::PHINode *) const;
  llvm::Optional<OneHotPhi> getOneHotPhi(llvm::PHINode *) const;

  bool isGatedPhi(llvm::PHINode *PN) const {
    return GatedPhis.count(PN);
  }
  // Check whether I is a the live-out of some sub-loop subvl, if so, return subvl
  VLoop *isLiveOutOfSubLoop(llvm::Instruction *I) const;

  // Get the incoming condition if the ith phi value
  const ControlCondition *getIncomingPhiCondition(llvm::PHINode *PN, unsigned i) {
    assert(GatedPhis.count(PN));
    return GatedPhis[PN][i];
  }

  static bool isSafeToCoIterate(const VLoop *, const VLoop *);
  static bool isSafeToFuse(VLoop *, VLoop *, llvm::ScalarEvolution &SE);

  bool haveIdenticalTripCounts(VLoop *, llvm::ScalarEvolution &);
  VLoop *getParent() const { return Parent; }
};

bool haveIdenticalTripCounts(const llvm::Loop *, const llvm::Loop *,
                             llvm::ScalarEvolution &);

#endif
