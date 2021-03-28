#include "EnumerateSeeds.h"
#include "InstSema.h"
#include "LaneBinding.h"
#include "Packer.h"
#include "llvm/IR/BasicBlock.h"

using namespace llvm;

namespace {

struct AbstractSeedHasher {
  static inline AbstractSeedPack getEmptyKey() { return {}; }
  static inline AbstractSeedPack getTombstoneKey() {
    return {(Canonicalizer::Node *)~0u};
  }
  static inline bool isEqual(AbstractSeedPack X, AbstractSeedPack Y) {
    return X == Y;
  }
  static inline unsigned getHashValue(const AbstractSeedPack &Seed) {
    return hash_combine_range(Seed.begin(), Seed.end());
  }
};

class Enumerator {
  Packer *Pkr;
  Canonicalizer *Canon;
  BasicBlock *BB;
  const MatchManager &MM;
  DenseMap<InstBinding *, std::unique_ptr<LaneBinding>> Bindings;
  DenseMap<AbstractSeedPack, bool, AbstractSeedHasher> Memo;
  const LaneBinding *getBinding(InstBinding *Inst) const {
    return Bindings.find(Inst)->second.get();
  }
  bool isFeasible(const AbstractSeedPack &);
  void enumerateRec(std::vector<AbstractSeedPack> &Seeds, unsigned LaneId,
                    AbstractSeedPack, ArrayRef<Canonicalizer::Node *>);

public:
  Enumerator(Packer *, Canonicalizer *, BasicBlock *);
  std::vector<AbstractSeedPack> enumerate(ArrayRef<Canonicalizer::Node *>);
};

bool isLeaf(ArrayRef<Value *> Operand, bool &IsFeasible) {
  IsFeasible = true;
  bool IsLeaf = false;
  for (auto *V : Operand) {
    if (!V)
      continue;
    IsLeaf |= !isa<Instruction>(V);
    IsFeasible &= isa<Constant>(V);
  }
  return IsLeaf;
}

} // namespace

Enumerator::Enumerator(Packer *Pkr, Canonicalizer *Canon, BasicBlock *BB)
    : Pkr(Pkr), Canon(Canon), BB(BB), MM(Pkr->getMatchManager(BB)) {
  for (auto *Inst : Pkr->getInsts())
    Bindings[Inst] = std::make_unique<LaneBinding>(Inst);
}

bool Enumerator::isFeasible(const AbstractSeedPack &Seed) {
  auto It = Memo.find(Seed);
  if (It != Memo.end())
    return It->second;

  bool AllLoads = true;
  for (const Canonicalizer::Node *N : Seed) {
    if (N && !isa<LoadInst>(N->getOneMember())) {
      AllLoads = false;
      break;
    }
  }
  if (AllLoads) {
    return Memo[Seed] = true;
  }

  unsigned NumLanes = Seed.size();
  bool Feasible = false;
  for (auto *Inst : Pkr->getInsts()) {
    ArrayRef<BoundOperation> LaneOps = Inst->getLaneOps();
    if (LaneOps.size() != NumLanes)
      continue;

    std::vector<const Operation::Match *> Lanes;
    for (unsigned i = 0; i < LaneOps.size(); i++) {
      if (!Seed[i]) {
        Lanes.push_back(nullptr);
        continue;
      }

      ArrayRef<Operation::Match> Matches =
          MM.getMatchesForOutput(LaneOps[i].getOperation(), Seed[i]->getOneMember());
      if (Matches.empty())
        break;
      Lanes.push_back(&Matches[0]);
    }
    if (Lanes.size() != NumLanes)
      continue;

    const LaneBinding *LB = getBinding(Inst);
    unsigned NumInputs = LB->getNumInputs();
    bool InstFeasible = true;
    for (unsigned i = 0; i < NumInputs; i++) {
      SmallVector<Value *, 8> Input;
      LB->apply(i, Lanes, Input);
      bool LeafIsFeasible;
      if (isLeaf(Input, LeafIsFeasible)) {
        if (LeafIsFeasible)
          continue;
        InstFeasible = false;
        break;
      }

      AbstractSeedPack AbstractInput;
      for (auto *V : Input) {
        AbstractInput.push_back(V ? Canon->get(cast<Instruction>(V)) : nullptr);
      }
      if (!isFeasible(AbstractInput)) {
        InstFeasible = false;
        break;
      }
    }
    if (InstFeasible) {
      Feasible = true;
      break;
    }
  }
  return Memo[Seed] = Feasible;
}

void Enumerator::enumerateRec(std::vector<AbstractSeedPack> &Seeds,
                              unsigned LaneId, AbstractSeedPack Seed,
                              ArrayRef<Canonicalizer::Node *> Nodes) {
  unsigned NumLanes = Seed.size();
  for (auto *N : Nodes) {
    Seed[LaneId] = N;
    if (!isFeasible(Seed))
      continue;

    if (LaneId + 1 < NumLanes)
      enumerateRec(Seeds, LaneId + 1, Seed, Nodes);
    else
      Seeds.push_back(Seed);
  }
}

std::vector<AbstractSeedPack>
Enumerator::enumerate(ArrayRef<Canonicalizer::Node *> Nodes) {
  std::vector<AbstractSeedPack> Seeds;
  for (unsigned VL : {4, 8, 16}) {
    AbstractSeedPack Seed(VL, nullptr);
    enumerateRec(Seeds, 0, Seed, Nodes);
  }
  return Seeds;
}

std::vector<AbstractSeedPack>
enumerateAbstractSeeds(Packer *Pkr, Canonicalizer *Canon, BasicBlock *BB,
                       ArrayRef<Canonicalizer::Node *> Nodes) {
  Enumerator E(Pkr, Canon, BB);
  return E.enumerate(Nodes);
}
