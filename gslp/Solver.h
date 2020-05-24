#ifndef SOLVER_H
#define SOLVER_H

#include "Packer.h"
#include "VectorPackContext.h"
#include "VectorPackSet.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/Hashing.h"
#include <bitset>

class PackEnumerationCache {
  // Mapping a focus instruction to the set of packs it can involve in,
  // Assumming every instruction before it is free and below not.
  llvm::DenseMap<llvm::Instruction *, std::vector<const VectorPack *>>
      FocusToPacksMap;

public:
  llvm::ArrayRef<const VectorPack *> getPacks(llvm::Instruction *I,
                                              bool &InCache) const {
    auto It = FocusToPacksMap.find(I);
    if (It != FocusToPacksMap.end()) {
      InCache = true;
      return It->second;
    }
    InCache = false;
    return {};
  }

  void insert(llvm::Instruction *I, std::vector<const VectorPack *> &&Packs) {
    FocusToPacksMap[I] = Packs;
  }
};

class MatchManager;
class Frontier {
  Packer *Pkr;
  friend struct FrontierHashInfo;
  llvm::BasicBlock *BB;
  const VectorPackContext *VPCtx;
  llvm::BasicBlock::reverse_iterator BBIt;
  std::vector<const OperandPack *> UnresolvedPacks;
  llvm::BitVector UnresolvedScalars;
  // Instructions we haven't assigned yet.
  llvm::BitVector FreeInsts;

  void freezeOneInst(unsigned);
  bool resolveOperandPack(const VectorPack &VP, const OperandPack &UP);
  void advanceBBIt();

  // Remove any packs that use frozen instructions.
  std::vector<const VectorPack *>
      filterFrozenPacks(llvm::ArrayRef<const VectorPack *>) const;

  // Check if `OP` has been resolved.
  bool resolved(const OperandPack &OP) const;

public:
  // Create the initial frontier, which surrounds the whole basic block
  Frontier(llvm::BasicBlock *BB, Packer *Pkr);
  std::unique_ptr<Frontier> advance(const VectorPack *VP, float &Cost,
                                    llvm::TargetTransformInfo *TTI) const;
  std::unique_ptr<Frontier> advance(llvm::Instruction *I, float &Cost,
                                    llvm::TargetTransformInfo *TTI) const;
  llvm::BasicBlock *getBasicBlock() const { return BB; }
  float advanceInplace(llvm::Instruction *, llvm::TargetTransformInfo *);
  float advanceInplace(const VectorPack *, llvm::TargetTransformInfo *);
  llvm::Instruction *getNextFreeInst() const;
  const llvm::BitVector &getFreeInsts() const { return FreeInsts; }
  std::vector<const VectorPack *>
  nextAvailablePacks(unsigned MaxNumLanes, unsigned EnumCap,
                     PackEnumerationCache *) const;
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
};

// Hashing support for `Frontier`
struct FrontierHashInfo {
  static Frontier *getEmptyKey() { return nullptr; }

  static Frontier *getTombstoneKey() { return reinterpret_cast<Frontier *>(1); }

  static unsigned getHashValue(const Frontier *Frt) {
    using namespace llvm;

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
  }

  static bool isTombstoneOrEmpty(const Frontier *Frt) {
    return Frt == getTombstoneKey() || Frt == getEmptyKey();
  }

  static bool isEqual(const Frontier *A, const Frontier *B) {
    if (isTombstoneOrEmpty(A) || isTombstoneOrEmpty(B))
      return A == B;

    return A->BB == B->BB && A->FreeInsts == B->FreeInsts &&
           A->UnresolvedScalars == B->UnresolvedScalars &&
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
  UCTNode *getNode(std::unique_ptr<Frontier> Frontier);
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
    const VectorPack *VP; // NULL means we choose Frt->getNextFreeInst();
    UCTNode *Next;
    uint64_t Count;
    float Cost; // Reward

    Transition(const VectorPack *VP, UCTNode *Next, float Cost)
        : VP(VP), Next(Next), Count(0), Cost(Cost) {}

    float visited() const { return Count > 0; }

    unsigned visitCount() const { return Count; }

    // Average Q value
    float avgCost() const { return Cost + Next->avgCost(); }
    float transitionCost() const { return Cost; }
  };

  std::atomic<std::vector<float> *> TransitionWeight;

  // Score a transition using the UCT2 formula from
  // ``Transpositions and Move Groups in Monte Carlo Tree Search''
  float score(const Transition &T, float C) const {
    return -normalize(T.avgCost()) +
           C * sqrt(logf(visitCount()) / float(T.visitCount()));
  }

private:
  std::vector<Transition> Transitions;

  UCTNode(const Frontier *Frt) : Frt(Frt), TotalCost(0), Count(0) {

    TransitionWeight.store(nullptr);
  }

public:
  float minCost() const { return CostRange->Min; }
  float maxCost() const { return CostRange->Max; }
  ~UCTNode() {
    auto Ptr = TransitionWeight.load();
    if (Ptr)
      delete Ptr;
  }

  // Fill out the out edge
  void expand(unsigned MaxNumLanes, unsigned EnumCap, UCTNodeFactory *Factory,
              PackEnumerationCache *EnumCache, llvm::TargetTransformInfo *);
  bool expanded() { return !Transitions.empty() && !isTerminal(); }
  bool isTerminal() const { return !Frt->getNextFreeInst(); }

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

// Interface for state evaluation
struct FrontierEvaluator {
  virtual float evaluate(unsigned MaxNumLanes, unsigned EnumCap,
                         const Frontier *Frt, PackEnumerationCache &EnumCache,
                         Packer *Pkr) = 0;
};

struct DummyEvaluator : public FrontierEvaluator {
  float evaluate(unsigned, unsigned, const Frontier *, PackEnumerationCache &,
                 Packer *) override {
    return 0;
  }
};

class RolloutEvaluator : public FrontierEvaluator {
  float evaluate(unsigned, unsigned, const Frontier *, PackEnumerationCache &,
                 Packer *) override;
};

// Interface for asynchronous policy prediction.
class PackingPolicy {
  unsigned MaxNumLanes;

public:
  PackingPolicy() = delete;
  PackingPolicy(unsigned MaxNumLanes) : MaxNumLanes(MaxNumLanes) {}
  virtual ~PackingPolicy() {}
  unsigned getMaxNumLanes() const { return MaxNumLanes; }
  // Predict transition probability *asynchronously*.
  // Result if is update asynchronously via `UCTNode::updateTransitionWeight`.
  virtual void predictAsync(UCTNode *) = 0;
  // Predict transition probability *synchronously*.
  virtual void predict(UCTNode *, std::vector<float> &) = 0;
  // Cancel prediction requests we made asynchronously.
  virtual void cancel() = 0;
};

class UCTSearch {
  // Controlling how much we explore.
  float C;
  // Controlling how much we trust the policy bias.
  float W;

  unsigned EnumCap;
  unsigned ExpandThreshold;

  UCTNodeFactory *Factory;
  Packer *Pkr;

  PackingPolicy *Policy;

  // How we evaluate a leaf UCTNode (e.g., w/ a value network or rollout)
  FrontierEvaluator *Evaluator;
  PackEnumerationCache EnumCache;
  llvm::TargetTransformInfo *TTI;

public:
  UCTSearch(float C, float W, unsigned EnumCap, unsigned ExpandThreshold,
            UCTNodeFactory *Factory, Packer *Pkr, PackingPolicy *Policy,
            FrontierEvaluator *Evaluator, llvm::TargetTransformInfo *TTI)
      : C(C), W(W), EnumCap(EnumCap), ExpandThreshold(ExpandThreshold),
        Factory(Factory), Pkr(Pkr), Policy(Policy), Evaluator(Evaluator),
        TTI(TTI) {}

  void run(UCTNode *Root, unsigned Iter);
  float evalLeafNode(UCTNode *N) {
    return Evaluator->evaluate(Policy ? Policy->getMaxNumLanes() : 8, EnumCap,
                               N->getFrontier(), EnumCache, Pkr);
  }
};

#endif
