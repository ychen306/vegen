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

class Frontier;
struct BackwardShuffle {
  virtual std::vector<const OperandPack *>
  run(const VectorPackContext *,
      llvm::ArrayRef<const OperandPack *> Outputs) const = 0;
  virtual float getCost(llvm::TargetTransformInfo *) const = 0;
};

struct ShuffleTask {
  const BackwardShuffle *Shfl;
  std::vector<const OperandPack *> Outputs;
  std::vector<const OperandPack *> Inputs;
  bool Feasible;
  ShuffleTask(const BackwardShuffle *Shfl,
              std::vector<const OperandPack *> Outputs, const Frontier *Frt);
  float getCost(llvm::TargetTransformInfo *TTI) const {
    return Shfl->getCost(TTI);
  }
  bool feasible() const { return Feasible; }
};

llvm::raw_ostream &operator<<(llvm::raw_ostream &, const ShuffleTask &);
llvm::raw_ostream &operator<<(llvm::raw_ostream &, const OperandPack &);

class MatchManager;
class Frontier {
  bool Shuffled = false;
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
                                    llvm::TargetTransformInfo *TTI,
                                    bool Shuffled = false) const;
  std::unique_ptr<Frontier> advance(llvm::Instruction *I, float &Cost,
                                    llvm::TargetTransformInfo *TTI) const;
  std::unique_ptr<Frontier> advance(ShuffleTask, float &Cost,
                                    llvm::TargetTransformInfo *TTI) const;
  llvm::BasicBlock *getBasicBlock() const { return BB; }
  float advanceInplace(llvm::Instruction *, llvm::TargetTransformInfo *);
  float advanceInplace(const VectorPack *, llvm::TargetTransformInfo *);
  float advanceInplace(ShuffleTask, llvm::TargetTransformInfo *);
  float replaceAllUnresolvedPacks(llvm::ArrayRef<const OperandPack *>,
                                  llvm::TargetTransformInfo *);
  const llvm::BitVector &getFreeInsts() const { return FreeInsts; }
  bool isFree(llvm::Instruction *I) const {
    return FreeInsts.test(VPCtx->getScalarId(I));
  }
  bool shuffled() const { return Shuffled; }
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

class PartialShuffle {
  // Any usable instruction in a frontier, eventually, should be either in the
  // set of new operands, or scalarized
  std::vector<llvm::BitVector> NewOperands;
  llvm::BitVector Scalarized;
  llvm::BitVector Decided;

public:
  PartialShuffle(const VectorPackContext *VPCtx, unsigned MaxNumOperands);
  float sample(Frontier &Frt) const;
  std::unique_ptr<PartialShuffle> scalarize(unsigned InstId) const {
    auto Next = std::make_unique<PartialShuffle>(*this);
    Next->Scalarized.set(InstId);
    Next->Decided.set(InstId);
    return Next;
  }
  void scalarizeMany(llvm::BitVector X) {
    Scalarized |= X;
    Decided |= X;
  }
  unsigned getNumOperands() const { return NewOperands.size(); }
  std::unique_ptr<PartialShuffle> addToOperand(unsigned InstId, unsigned OperandId) const {
    auto Next = std::make_unique<PartialShuffle>(*this);
    Next->NewOperands[OperandId].set(InstId);
    Next->Decided.set(InstId);
    return Next;
  }
  llvm::BitVector getUndecided(const Frontier &Frt) const { 
    auto Undecided = Decided;
    Undecided.flip();
    Undecided &= Frt.usableInstIds();
    return Undecided;
  }
  const llvm::BitVector getScalarized() const { return Scalarized; }
  std::vector<const OperandPack *> getOperandPacks(const VectorPackContext *) const;
};

// Hashing support for `Frontier`
struct FrontierHashInfo {
  static Frontier *getEmptyKey() { return nullptr; }

  static Frontier *getTombstoneKey() { return reinterpret_cast<Frontier *>(1); }

  static unsigned getHashValue(const Frontier *Frt) {
    using namespace llvm;

    if (Frt == getEmptyKey()) {
      return ~0;
    } else if (Frt == getTombstoneKey()) {
      return ~1;
    }
    return Frt->Hash;
  }

  static bool isTombstoneOrEmpty(const Frontier *Frt) {
    return Frt == getTombstoneKey() || Frt == getEmptyKey();
  }

  static bool isEqual(const Frontier *A, const Frontier *B) {
    if (isTombstoneOrEmpty(A) || isTombstoneOrEmpty(B))
      return A == B;

    return A->BB == B->BB && A->Shuffled == B->Shuffled &&
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
  UCTNode *getNode(const Frontier *, const PartialShuffle *);
};

class UCTNode {
  friend class UCTNodeFactory;

  // State
  const Frontier *Frt;
  const PartialShuffle *PS;

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
    llvm::Optional<ShuffleTask> ST;
    std::unique_ptr<PartialShuffle> PS;
    UCTNode *Next;
    uint64_t Count;
    float Cost; // Reward
    float Bias{0};
    bool DisableShuffling;

    Transition(const VectorPack *VP, bool DisableShuffling = false)
        : I(nullptr), VP(VP), Next(nullptr), Count(0),
          DisableShuffling(DisableShuffling) {}

    Transition(llvm::Instruction *I)
        : VP(nullptr), I(I), Next(nullptr), Count(0), DisableShuffling(true) {}

    Transition(ShuffleTask ST)
        : VP(nullptr), I(nullptr), ST(ST), Next(nullptr), Count(0),
          DisableShuffling(false) {}

    Transition(std::unique_ptr<PartialShuffle> PS)
        : VP(nullptr), I(nullptr), PS(std::move(PS)), Next(nullptr), Count(0), DisableShuffling(false) {}

    float visited() const { return Count > 0; }

    unsigned visitCount() const { return Count; }

    UCTNode *getNext(UCTNode *Parent, UCTNodeFactory *Factory,
                     llvm::TargetTransformInfo *TTI) {
      if (Next)
        return Next;

      if (VP)
        Next = Factory->getNode(
            Parent->getFrontier()->advance(VP, Cost, TTI, DisableShuffling));
      else if (I)
        Next = Factory->getNode(Parent->getFrontier()->advance(I, Cost, TTI));
      else if (ST)
        Next = Factory->getNode(
            Parent->getFrontier()->advance(ST.getValue(), Cost, TTI));
      else {
        Cost = 0;
        if (PS->getUndecided(*Parent->getFrontier()).count())
          Next = Factory->getNode(Parent->getFrontier(), PS.get());
        else {
          using namespace llvm;
          // We've completed this partial shuffle
          auto Frt = std::make_unique<Frontier>(*Parent->getFrontier());
          auto *VPCtx = Frt->getContext();
          BitVector Scalarized = PS->getScalarized();
          for (unsigned i : Scalarized.set_bits()) {
            Cost += Frt->advanceInplace(cast<Instruction>(VPCtx->getScalar(i)), TTI);
          }
          auto OperandPacks = PS->getOperandPacks(VPCtx);
          Cost += Frt->replaceAllUnresolvedPacks(OperandPacks, TTI);
          Next = Factory->getNode(std::move(Frt));
        }
      }

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
      : Frt(Frt), PS(nullptr), TotalCost(0), Count(0),
        TransitionWeight(nullptr), IsTerminal(false) {}
  UCTNode(const Frontier *Frt, const PartialShuffle *PS)
      : Frt(Frt), PS(PS), TotalCost(0), Count(0),
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
  void expand();
  bool expanded() { return !Transitions.empty() && !isTerminal(); }
  bool isTerminal() const {
    return Frt->getFreeInsts().count() == 0 || IsTerminal;
  }

  std::vector<Transition> &transitions() { return Transitions; }

  float avgCost() const { return TotalCost / float(Count); }

  uint64_t visitCount() const { return Count; }
  const Frontier *getFrontier() const { return Frt; }
  const PartialShuffle *getPartialShuffle() const { return PS; }
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
  virtual float evaluate(const Frontier *Frt) = 0;
};

struct DummyEvaluator : public FrontierEvaluator {
  float evaluate(const Frontier *) override { return 0; }
};

class RolloutEvaluator : public FrontierEvaluator {
  llvm::DenseMap<const Frontier *, std::vector<VectorPack *>, FrontierHashInfo>
      ExtensionCache;
  std::vector<std::unique_ptr<Frontier>> Frontiers;
  std::vector<VectorPack *> getExtensions(const Frontier &);

public:
  float evaluate(const Frontier *) override;
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

  unsigned ExpandThreshold;

  UCTNodeFactory *Factory;
  Packer *Pkr;

  PackingPolicy *Policy;

  // How we evaluate a leaf UCTNode (e.g., w/ a value network or rollout)
  FrontierEvaluator *Evaluator;
  PackEnumerationCache EnumCache;
  llvm::TargetTransformInfo *TTI;

public:
  UCTSearch(float C, float W, unsigned ExpandThreshold, UCTNodeFactory *Factory,
            Packer *Pkr, PackingPolicy *Policy, FrontierEvaluator *Evaluator,
            llvm::TargetTransformInfo *TTI)
      : C(C), W(W), ExpandThreshold(ExpandThreshold), Factory(Factory),
        Pkr(Pkr), Policy(Policy), Evaluator(Evaluator), TTI(TTI) {}

  void run(UCTNode *Root, unsigned Iter);
  float evalLeafNode(UCTNode *N);
};

class VectorPackSet;
float optimizeBottomUp(VectorPackSet &, Packer *, llvm::BasicBlock *);

#endif
