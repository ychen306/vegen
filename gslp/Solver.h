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
  Frontier(llvm::BasicBlock *BB, const VectorPackContext *VPCtx);
  std::unique_ptr<Frontier> advance(const VectorPack *VP, float &Cost,
                                    llvm::TargetTransformInfo *TTI) const;
  std::unique_ptr<Frontier> advance(llvm::Instruction *I, float &Cost,
                                    llvm::TargetTransformInfo *TTI) const;
  llvm::BasicBlock *getBasicBlock() const { return BB; }
  float advanceInplace(llvm::Instruction *, llvm::TargetTransformInfo *);
  float advanceInplace(const VectorPack *, llvm::TargetTransformInfo *);
  llvm::Instruction *getNextFreeInst() const;
  llvm::BitVector getFreeInsts() const { return FreeInsts; }
  std::vector<const VectorPack *>
  nextAvailablePacks(Packer *, PackEnumerationCache *) const;
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

    // Average Q value
    float avgCost() const { return Cost + Next->avgCost(); }

    // The ucb bias for this transition
    float bias(uint64_t ParentCount, float C) const {
      return C * sqrtf(logf(ParentCount) / float(Count));
    }

    // UCT2 formula from the paper
    // ``Transpositions and Move Groups in Monte Carlo Tree Search''
    float score(uint64_t ParentCount, float C) const {
      return -avgCost() + bias(ParentCount, C);
    }
  };

private:
  std::vector<Transition> Transitions;

  UCTNode(const Frontier *Frt) : Frt(Frt), TotalCost(0), Count(0) {}

public:
  // Fill out the out edge
  void expand(UCTNodeFactory *Factory, Packer *Pkr,
              PackEnumerationCache *EnumCache, llvm::TargetTransformInfo *);
  bool expanded() { return !Transitions.empty() && !isTerminal(); }
  bool isTerminal() const { return !Frt->getNextFreeInst(); }
  std::vector<Transition> &transitions() { return Transitions; }

  float avgCost() const { return TotalCost / float(Count); }

  uint64_t visitCount() const { return Count; }
  const Frontier *getFrontier() const { return Frt; }
  void update(float Cost) {
    TotalCost += Cost;
    Count++;
  }
};

// Interface for state evaluation
struct FrontierEvaluator {
  virtual float evaluate(const Frontier *Frt, PackEnumerationCache &EnumCache,
                         Packer *Pkr) = 0;
};

struct DummyEvaluator : public FrontierEvaluator {
  float evaluate(const Frontier *Frt, PackEnumerationCache &EnumCache,
                 Packer *Pkr) override {
    return 0;
  }
};

class RolloutEvaluator : public FrontierEvaluator {
  float evaluate(const Frontier *Frt, PackEnumerationCache &EnumCache,
                 Packer *Pkr) override;
};


struct PackingPolicy {
  // Interface for policy prediction.
  virtual void predict(const Frontier *Frt, llvm::ArrayRef<UCTNode::Transition> Transitions, std::vector<float> &Prob) = 0;
};

class UCTSearch {
  // The exploration factor in UCT
  float C;

  UCTNodeFactory *Factory;
  Packer *Pkr;

  PackingPolicy *Policy;
  
  // How we evaluate a leaf UCTNode (e.g., w/ a value network or rollout)
  FrontierEvaluator *Evaluator;
  PackEnumerationCache EnumCache;
  llvm::TargetTransformInfo *TTI;

public:
  UCTSearch(float C, UCTNodeFactory *Factory, Packer *Pkr,
      PackingPolicy *Policy,
            FrontierEvaluator *Evaluator, llvm::TargetTransformInfo *TTI)
      : C(C), Factory(Factory), Pkr(Pkr), Policy(Policy), Evaluator(Evaluator), TTI(TTI) {}

  void run(UCTNode *Root, unsigned Iter);
  float evalLeafNode(UCTNode *N) {
    return Evaluator->evaluate(N->getFrontier(), EnumCache, Pkr);
  }
};

#endif
