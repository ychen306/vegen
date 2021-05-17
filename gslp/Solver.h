#ifndef SOLVER_H
#define SOLVER_H

#include "Packer.h"
#include "CandidatePackSet.h"
#include "VectorPackContext.h"
#include "VectorPackSet.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/Hashing.h"
#include <bitset>

llvm::raw_ostream &operator<<(llvm::raw_ostream &, const OperandPack &);

class MatchManager;
class Frontier {
  Packer *Pkr;
  friend struct FrontierHashInfo;
  llvm::BasicBlock *BB;
  const VectorPackContext *VPCtx;
  std::vector<const OperandPack *> UnresolvedPacks;
  llvm::BitVector UnresolvedScalars;
  // Instructions we haven't assigned yet.
  llvm::BitVector FreeInsts;
  // Free insts without free users
  llvm::BitVector UsableInsts;

  void freezeOneInst(llvm::Instruction *);
  bool resolveOperandPack(const VectorPack &VP, const OperandPack &UP);

  // Check if `OP` has been resolved.
  bool resolved(const OperandPack &OP) const;
  unsigned Hash;

public:
  // Create the initial frontier, which surrounds the whole basic block
  Frontier(llvm::BasicBlock *BB, Packer *Pkr);
  std::unique_ptr<Frontier> advance(const VectorPack *VP, float &Cost,
                                    llvm::TargetTransformInfo *TTI) const;
  std::unique_ptr<Frontier> advance(llvm::Instruction *I, float &Cost,
                                    llvm::TargetTransformInfo *TTI) const;
  void shrinkFor(llvm::BitVector R);
  llvm::BasicBlock *getBasicBlock() const { return BB; }
  float advanceInplace(llvm::Instruction *, llvm::TargetTransformInfo *);
  float advanceInplace(const VectorPack *, llvm::TargetTransformInfo *);
  const llvm::BitVector &getFreeInsts() const { return FreeInsts; }
  bool isFree(llvm::Instruction *I) const {
    return FreeInsts.test(VPCtx->getScalarId(I));
  }
  llvm::ArrayRef<const OperandPack *> getUnresolvedPacks() const {
    return UnresolvedPacks;
  }
  llvm::iterator_range<VectorPackContext::value_iterator>
  getUnresolvedScalars() const {
    return VPCtx->iter_values(UnresolvedScalars);
  }
  unsigned numUnresolvedScalars() const { return UnresolvedScalars.count(); }
  Packer *getPacker() const { return Pkr; }
  bool isUsable(llvm::Instruction *I) const {
    // FIXME: deal with PHINode properly
    if (llvm::isa<llvm::PHINode>(I))
      return isFree(I);
    return UsableInsts.test(VPCtx->getScalarId(I));
  }

  llvm::iterator_range<VectorPackContext::value_iterator> usableInsts() const {
    return VPCtx->iter_values(UsableInsts);
  }
  const llvm::BitVector &usableInstIds() const { return UsableInsts; }

  unsigned numUsableInsts() const { return UsableInsts.count(); }
  const VectorPackContext *getContext() const { return VPCtx; }
};

// Hashing support for `Frontier`
struct FrontierHashInfo {
  static Frontier *getEmptyKey() { return nullptr; }

  static Frontier *getTombstoneKey() { return reinterpret_cast<Frontier *>(1); }

  static unsigned getHashValue(const Frontier *Frt) {
    using namespace llvm;
#if 1

    if (Frt == getEmptyKey()) {
      return ~0;
    } else if (Frt == getTombstoneKey()) {
      return ~1;
    }
    return Frt->Hash;
#else
    if (Frt == getEmptyKey()) {
      return hash_combine(reinterpret_cast<BasicBlock *>(0),
          ArrayRef<uint64_t>(), ArrayRef<uint64_t>(),
          ArrayRef<const OperandPack *>());
    } else if (Frt == getTombstoneKey()) {
      return hash_combine(reinterpret_cast<BasicBlock *>(1),
          ArrayRef<uint64_t>(), ArrayRef<uint64_t>(),
          ArrayRef<const OperandPack *>());
    }

    return hash_combine(reinterpret_cast<BasicBlock *>(2),
        Frt->UnresolvedScalars.getData(),
        Frt->FreeInsts.getData(),
        ArrayRef<const OperandPack *>(Frt->UnresolvedPacks));
#endif
  }

  static bool isTombstoneOrEmpty(const Frontier *Frt) {
    return Frt == getTombstoneKey() || Frt == getEmptyKey();
  }

  static bool isEqual(const Frontier *A, const Frontier *B) {
    if (isTombstoneOrEmpty(A) || isTombstoneOrEmpty(B))
      return A == B;

    return A->BB == B->BB && 
      A->FreeInsts == B->FreeInsts &&
      A->UnresolvedScalars == B->UnresolvedScalars &&
      A->UsableInsts == B->UsableInsts &&
      A->UnresolvedPacks == B->UnresolvedPacks;
  }
};

class UCTNode;
class UCTNodeFactory {
  std::vector<std::unique_ptr<Frontier>> Frontiers;
  std::vector<std::unique_ptr<UCTNode>> Nodes;
  llvm::DenseMap<Frontier *, UCTNode *, FrontierHashInfo> FrontierToNodeMap;

  public:
  UCTNodeFactory() : FrontierToNodeMap(1000000) {}
  UCTNode *getNode(std::unique_ptr<Frontier>);
};

class UCTNode {
  friend class UCTNodeFactory;

  // State
  const Frontier *Frt;

  // Return
  float TotalCost;
  uint64_t Count;

  // Record the max and min cost ever encountered starting from this node.
  // We use this to normalize cost,
  // which is necessary for the exploration factor to be meaningful.
  struct Range {
    float Min, Max;
    float range() const { return Max - Min; }
  };
  llvm::Optional<Range> CostRange;
  float normalize(float Cost) const {
    if (!CostRange || CostRange->Min == CostRange->Max)
      return 1.0;
    return (Cost - CostRange->Min) / CostRange->range();
  }

  public:
  // The next action state pair
  struct Transition {
    // If non-null then we've finished filling out a pack w/ this transition
    const VectorPack *VP;
    llvm::Instruction *I;
    UCTNode *Next;
    uint64_t Count;
    float Cost; // Reward
    float Bias{0};

    Transition(const VectorPack *VP)
      : I(nullptr), VP(VP), Next(nullptr), Count(0) {}

    Transition(llvm::Instruction *I)
      : VP(nullptr), I(I), Next(nullptr), Count(0) {}

    float visited() const { return Count > 0; }

    unsigned visitCount() const { return Count; }

    UCTNode *getNext(UCTNode *Parent, UCTNodeFactory *Factory,
        llvm::TargetTransformInfo *TTI) {
      if (Next)
        return Next;

      if (VP)
        Next = Factory->getNode(
            Parent->getFrontier()->advance(VP, Cost, TTI));
      else if (I)
        Next = Factory->getNode(Parent->getFrontier()->advance(I, Cost, TTI));

      assert(Next);

      return Next;
    }

    // Average Q value
    float avgCost() const { return Cost + Next->avgCost(); }
    float transitionCost() const { return Cost; }
  };

  std::atomic<std::vector<float> *> TransitionWeight;

  // Score a transition using the UCT2 formula from
  // ``Transpositions and Move Groups in Monte Carlo Tree Search''
  float score(const Transition &T, float C) const {
    return -normalize(T.avgCost()) +
      C * sqrt(logf(visitCount()) / float(T.visitCount())) +
      T.Bias / float(T.visitCount());
  }

  private:
  std::vector<Transition> Transitions;

  bool IsTerminal;

  UCTNode(const Frontier *Frt)
    : Frt(Frt), TotalCost(0), Count(0),
    TransitionWeight(nullptr), IsTerminal(false) {}
  public:
  float minCost() const { return CostRange->Min; }
  float maxCost() const { return CostRange->Max; }
  ~UCTNode() {
    auto Ptr = TransitionWeight.load();
    if (Ptr)
      delete Ptr;
  }

  // Fill out the out edge
  void expand(const CandidatePackSet *);
  bool expanded() { return !Transitions.empty() && !isTerminal(); }
  bool isTerminal() const {
    return Frt->getFreeInsts().count() == 0 || IsTerminal;
  }

  std::vector<Transition> &transitions() { return Transitions; }

  float avgCost() const { return TotalCost / float(Count); }

  uint64_t visitCount() const { return Count; }
  const Frontier *getFrontier() const { return Frt; }
  void update(float Cost) {
    TotalCost += Cost;

    if (CostRange) {
      CostRange->Min = std::min<float>(CostRange->Min, Cost);
      CostRange->Max = std::max<float>(CostRange->Max, Cost);
    } else {
      CostRange = {Cost, Cost};
    }

    Count++;
  }

  void updateTransitionWeight(std::vector<float> *NewWeight) {
    TransitionWeight.store(NewWeight);
  }

  llvm::ArrayRef<float> transitionWeight() {
    auto *WeightPtr = TransitionWeight.load();
    if (WeightPtr)
      return *WeightPtr;
    return llvm::ArrayRef<float>();
  }

  Packer *getPacker() const { return Frt->getPacker(); }
  static inline bool compareByVisitCount(const UCTNode::Transition &A,
      const UCTNode::Transition &B) {
    return A.visitCount() < B.visitCount();
  }
};

class VectorPackSet;
float optimizeBottomUp(VectorPackSet &, Packer *, llvm::BasicBlock *);

#endif
