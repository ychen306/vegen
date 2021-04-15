#include "EnumerateSeeds.h"
#include "InstSema.h"
#include "LaneBinding.h"
#include "Packer.h"
#include "llvm/IR/BasicBlock.h"

using namespace llvm;

namespace {

struct MatchInput {
  const Operation *Op;
  unsigned InputId;

  MatchInput(const InstBinding *Inst, const LaneBinding::InputRef &Input)
      : Op(Inst->getLaneOps()[Input.getMatchIdx()].getOperation()),
        InputId(Input.getInputIdx()) {}
};

//using ValuePath = std::vector<MatchInput>;
class ValuePath {
  std::vector<MatchInput> Path;
  mutable DenseMap<Instruction *, Value*> Values;
public:
  ValuePath() = default;
  ValuePath(MatchInput M) : Path({M}) {}
  ValuePath extend(const ValuePath &Other) const {
    ValuePath New = *this;
    New.Path.insert(New.Path.end(), Other.Path.begin(), Other.Path.end());
    return New;
  }
  Value *evaluate(Instruction *I, const MatchManager &MM) const {
    auto &V = Values[I];
    if (!V) {
      V = I;
      for (const MatchInput &M : Path)
        V = MM.getMatchesForOutput(M.Op, V).front().Inputs[M.InputId];
    }
    return V;
  }
};

class AbstractLeafPack {
  SmallVector<LaneBinding::Label, 8> Labels;
  SmallVector<Optional<ValuePath>, 8> Values;

public:
  AbstractLeafPack(unsigned N) : Labels(N), Values(N, ValuePath()) {
    std::iota(Labels.begin(), Labels.end(), 0);
  }

  // produce a seed pack according to some lane binding rule,
  // and get the `i'th seed/input
  AbstractLeafPack(const InstBinding *Inst, const LaneBinding *LB, unsigned i) {
    LB->label(i, Labels);
    for (Optional<LaneBinding::InputRef> Ref : LB->getInput(i)) {
      Values.push_back(None);
      if (Ref)
        Values.back() = MatchInput(Inst, *Ref);
    }
  }

  unsigned size() const { return Labels.size(); }
  Value *getValue(ArrayRef<Instruction *> Seed, unsigned i,
                  const MatchManager &MM, Canonicalizer *Canon) const {
    // This leaf value is don't care
    if (!Labels[i].hasValue())
      return nullptr;

    unsigned SeedLane = *Labels[i];
    // Seed value is null
    if (SeedLane < Seed.size() && Seed[SeedLane]) {
      // errs() << "ROOT IS IN CLASS " << Canon->get(Seed[SeedLane]) << '\n';
      return Values[i]->evaluate(Seed[SeedLane], MM);
    }
    return nullptr;
  }

  // suppose `this` is oriented w.r.t. `Other` (e.g., `Other` is the seed of
  // `this`) translate `this` so that it's oriented w.r.t. to the seed of
  // `Other`.
  AbstractLeafPack translate(const AbstractLeafPack &Other) const {
    auto New = *this;
    for (unsigned i = 0; i < Labels.size(); i++) {
      auto &L = Labels[i];
      if (!L || !Other.Labels[*L]) {
        New.Labels[i] = None;
        New.Values[i] = None;
      } else {
        New.Labels[i] = Other.Labels[*L];
        New.Values[i] = Other.Values[*L]->extend(*Values[i]);
      }
    }
    return New;
  }

  friend raw_ostream &operator<<(llvm::raw_ostream &OS,
                                 const AbstractLeafPack &Leaf) {
    OS << "LEAF {\n";
    auto &Labels = Leaf.Labels;
    auto &Values = Leaf.Values;
    for (unsigned i = 0; i < Labels.size(); i++) {
      OS << '\t';
      auto &L = Labels[i];
      if (L) {
        OS << *L << "  ";
#if 0
        for (const MatchInput &M : *Values[i])
          OS << M.InputId << ' ';
        OS << '\n';
#endif
      } else {
        OS << " ";
      }
    }
    OS << '}';
    return OS;
  }
};

using AbstractSeedPack = std::vector<const Canonicalizer::Node *>;

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
  const AccessLayoutInfo &LayoutInfo;
  DenseMap<InstBinding *, std::unique_ptr<LaneBinding>> Bindings;
  DenseMap<AbstractSeedPack, std::unique_ptr<std::vector<AbstractLeafPack>>,
           AbstractSeedHasher>
      Memo;
  const LaneBinding *getBinding(InstBinding *Inst) {
    auto &LB = Bindings[Inst];
    if (!LB)
      LB.reset(new LaneBinding(Inst));
    return LB.get();
  }
  // return the list of leaf packs as witness of feasiblity
  ArrayRef<AbstractLeafPack> checkFeasibility(const AbstractSeedPack &);
  void enumerateRec(std::vector<AbstractSeedPack> &Seeds, unsigned LaneId,
                    AbstractSeedPack, ArrayRef<Canonicalizer::Node *>);
  // Fraction of the pairs that are out-of-place in a leaf pack
  float computeEntropy(ArrayRef<Value *>);

  void printLeaves(const AbstractSeedPack &, ArrayRef<Instruction *>);

public:
  // estimate the cost of instantiatinga abstract seed pack
  float getCost(const AbstractSeedPack &, ArrayRef<Instruction *>,
                float Coeff = 0.2);
  Enumerator(Packer *, Canonicalizer *, BasicBlock *);
  std::vector<AbstractSeedPack> enumerate(ArrayRef<Canonicalizer::Node *>);
  void concretize(std::vector<OperandPack> &, const AbstractSeedPack &,
                  unsigned BeamWidth = 32);
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
    : Pkr(Pkr), Canon(Canon), BB(BB), MM(Pkr->getMatchManager(BB)),
      LayoutInfo(Pkr->getLoadInfo(BB)) {}

ArrayRef<AbstractLeafPack>
Enumerator::checkFeasibility(const AbstractSeedPack &Seed) {
  auto It = Memo.find(Seed);
  if (It != Memo.end())
    return *It->second;

  bool AllLoads = true;
  for (const Canonicalizer::Node *N : Seed)
    if (N && !isa<LoadInst>(N->getOneMember())) {
      AllLoads = false;
      break;
    }

  auto &Leaves =
      *(Memo[Seed] = std::make_unique<std::vector<AbstractLeafPack>>());

  if (AllLoads) {
    Leaves.emplace_back(Seed.size());
    return Leaves;
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

      ArrayRef<Operation::Match> Matches = MM.getMatchesForOutput(
          LaneOps[i].getOperation(), Seed[i]->getOneMember());
      if (Matches.empty())
        break;
      Lanes.push_back(&Matches[0]);
    }
    if (Lanes.size() != NumLanes) {
      continue;
    }

    const LaneBinding *LB = getBinding(Inst);
    unsigned NumInputs = LB->getNumInputs();
    Leaves.clear();
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

      auto ChildLabels = checkFeasibility(AbstractInput);
      if (ChildLabels.empty()) {
        InstFeasible = false;
        break;
      }
      // TODO: change this constructor... its only purpose is feed into
      // AbstractLeafPack::translate
      AbstractLeafPack LocalLeaf(Inst, LB, i);
      for (auto &L : ChildLabels)
        Leaves.push_back(L.translate(LocalLeaf));
    }
    if (InstFeasible) {
      Feasible = true;
      break;
    }
  }

  if (!Feasible)
    Leaves.clear();

  return Leaves;
}

void Enumerator::enumerateRec(std::vector<AbstractSeedPack> &Seeds,
                              unsigned LaneId, AbstractSeedPack Seed,
                              ArrayRef<Canonicalizer::Node *> Nodes) {
  unsigned NumLanes = Seed.size();
  for (auto *N : Nodes) {
    Seed[LaneId] = N;
    if (checkFeasibility(Seed).empty())
      continue;

    if (LaneId + 1 < NumLanes)
      enumerateRec(Seeds, LaneId + 1, Seed, Nodes);
    else {
      Seeds.push_back(Seed);
#if 0
      auto Leaves = checkFeasibility(Seed);
      errs() << "==============\n";
      for (auto &L : Leaves) {
        errs() << L << '\n';
      }
#endif
    }
  }
}

// TODO: Add utilization term?
float Enumerator::computeEntropy(ArrayRef<Value *> Pack) {
  struct Range {
    bool Initialized;
    unsigned Lo, Hi;

    Range() : Initialized(false) {}

    unsigned size() const { return Hi - Lo + 1; }

    void update(unsigned X) {
      if (Initialized) {
        if (Lo > X)
          Lo = X;
        if (Hi < X)
          Hi = X;
      } else {
        Initialized = true;
        Lo = Hi = X;
      }
    }
  };
  SmallMapVector<Instruction *, Range, 4> Ranges;

  Optional<unsigned> MaxId, MinId;

  float Error = 0;
  for (unsigned i = 0; i < Pack.size(); i++) {
    if (!Pack[i])
      continue;
    Optional<AccessLayoutInfo::AddressInfo> Info1 = None;
    if (auto *LI = dyn_cast<LoadInst>(Pack[i])) {
      Info1 = LayoutInfo.get(LI);
      Ranges[Info1->Leader].update(Info1->Id);
      if (MaxId) {
        MaxId = std::max(*MaxId, Info1->Id);
        MinId = std::min(*MinId, Info1->Id);
      } else {
        MaxId = Info1->Id;
        MinId = Info1->Id;
      }
    }
    for (unsigned j = i + 1; j < Pack.size(); j++) {
      if (!Pack[j])
        continue;
      Optional<AccessLayoutInfo::AddressInfo> Info2 = None;
      if (auto *LI = dyn_cast<LoadInst>(Pack[j]))
        Info2 = LayoutInfo.get(LI);
      if (isa<Constant>(Pack[i]) && isa<Constant>(Pack[j]))
        continue;
      if (!Info1 || !Info2 || Info1->Leader != Info2->Leader ||
          int(Info1->Id) - int(Info2->Id) != int(i) - int(j))
        Error += 1;
    }
  }

  float Utilization = 0;
  for (auto &KV : Ranges) {
    const Range &R = KV.second;
    Utilization += std::min<float>(1.0, float(Pack.size()) / float(R.size()));
  }

  float N = Pack.size();
  unsigned Util = 0;
  if (MaxId)
    Util = float(*MaxId - *MinId + 1) / float(Pack.size()) - 1;
  return Error / (N * (N - 1) / 2) + Util;// + Ranges.size() - Utilization;
}

void Enumerator::printLeaves(const AbstractSeedPack &Seed,
                             ArrayRef<Instruction *> SeedValues) {
  auto Leafs = checkFeasibility(Seed);
  errs() << "<<<<<<<<< LEAVES >>>>>>>>>>>\n";
  for (auto &Leaf : Leafs) {
    for (unsigned i = 0; i < Leaf.size(); i++) {
      Value *V = Leaf.getValue(SeedValues, i, MM, Canon);
      if (auto *LI = dyn_cast_or_null<LoadInst>(V))
        errs() << LayoutInfo.get(LI).Id << ' ';
      else
        errs() << "-1 ";
    }
    errs() << '\n';
  }
  errs() << "<<<<< SEED >>>>\n";
  for (auto *I : SeedValues) {
    if (!I) {
      errs() << "-1 ";
      continue;
    }
    bool Printed = false;
    for (User *U : I->users())
      if (auto *SI = dyn_cast<StoreInst>(U)) {
        errs() << Pkr->getStoreInfo(BB).get(SI).Id << ' ';
        Printed = true;
        break;
      }
    if (!Printed)
      errs() << "-1 ";
  }
  errs() << "\n\n";
}

float Enumerator::getCost(const AbstractSeedPack &Seed,
                          ArrayRef<Instruction *> SeedValues, float Coeff) {
  assert(SeedValues.size() <= Seed.size());
  auto Leafs = checkFeasibility(Seed);
  assert(!Leafs.empty());
  float Cost = 0;

  using ValueList = SmallVector<Value *, 8>;
  struct ListHasher {
    static inline ValueList getEmptyKey() { return ValueList(); }
    static inline ValueList getTombstoneKey() {
      return {reinterpret_cast<Value *>(~0u)};
    }
    static inline bool isEqual(const ValueList &A, const ValueList &B) {
      if (A.size() != B.size())
        return false;
      for (unsigned i = 0; i < A.size(); i++)
        if (A[i] != B[i])
          return false;
      return true;
    }
    static inline unsigned getHashValue(const ValueList &X) {
      return hash_combine_range(X.begin(), X.end());
    }
  };
  DenseSet<ValueList, ListHasher> Visited;

  for (auto &Leaf : Leafs) {
    ValueList LeafValues;
    for (unsigned i = 0; i < Leaf.size(); i++) {
      // errs() << "Getting leaf value at lane " << i << '\n';
      LeafValues.push_back(Leaf.getValue(SeedValues, i, MM, Canon));
    }
    bool Inserted = Visited.insert(LeafValues).second;
    if (Inserted)
      Cost += computeEntropy(LeafValues);
  }

  {
    std::vector<StoreInst *> Stores;
    for (auto *I : SeedValues) {
      Stores.push_back(nullptr);
      for (User *U : I->users())
        if (auto *SI = dyn_cast<StoreInst>(U)) {
          Stores.back() = SI;
          break;
        }
    }

    float Error = 0;
    for (unsigned i = 0; i < Stores.size(); i++) {
      if (!Stores[i])
        continue;
      auto &LayoutInfo = Pkr->getStoreInfo(BB);
      auto Info1 = LayoutInfo.get(Stores[i]);
      for (unsigned j = i + 1; j < Stores.size(); j++) {
        if (!Stores[j])
          continue;
        auto Info2 = LayoutInfo.get(Stores[j]);
        if (Info1.Leader != Info2.Leader ||
            int(Info1.Id) - int(Info2.Id) != int(i) - int(j))
          Error += 1;
      }
    }
    // return Error;
    float N = Stores.size();
    Cost += Error * (N * (N - 1) / 2);
  }

  return Cost;
}

std::vector<AbstractSeedPack>
Enumerator::enumerate(ArrayRef<Canonicalizer::Node *> Nodes) {
  std::vector<AbstractSeedPack> Seeds;
  for (unsigned VL : {4, 8, 16, 32}) {
    AbstractSeedPack Seed(VL, nullptr);
    enumerateRec(Seeds, 0, Seed, Nodes);
  }
  return Seeds;
}

void Enumerator::concretize(std::vector<OperandPack> &ConcreteSeeds,
                            const AbstractSeedPack &Seed, unsigned BeamWidth) {
  struct Candidate {
    BitVector Used;
    SmallVector<Instruction *, 8> Insts;
    float Cost;
    bool operator<(const Candidate Other) const { return Cost < Other.Cost; }
  };

  auto *VPCtx = Pkr->getContext(BB);

  auto ExtendCandidate = [&](const Candidate &C, Instruction *I) -> Candidate {
    auto C2 = C;
    C2.Insts.push_back(I);
    C2.Used.set(VPCtx->getScalarId(I));
    C2.Cost = getCost(Seed, C2.Insts);
    return C2;
  };
  auto EmptyCandidate = [&](BitVector Used) -> Candidate {
    return Candidate{Used, {}, 0};
  };
  auto CanExtendWith = [&](const Candidate &C, Instruction *I) -> bool {
    return !C.Used.test(VPCtx->getScalarId(I));
  };

  // FIXME: enumerate a set of packs instead of a single pack,
  // the set of packs to be maximally disjoint
  // for (auto *X : Seed[0]->Members) {
  BitVector Used(VPCtx->getNumValues());
  for (;;) {
    std::vector<Candidate> Candidates {EmptyCandidate(Used)};
    for (unsigned i = 0; i < Seed.size(); i++) {
      std::vector<Candidate> NextCandidates;
      for (const Candidate &C : Candidates)
        for (auto *I : Seed[i]->Members)
          if (CanExtendWith(C, I))
            NextCandidates.push_back(ExtendCandidate(C, I));

      std::sort(NextCandidates.begin(), NextCandidates.end());
      if (NextCandidates.size() > BeamWidth)
        NextCandidates.resize(BeamWidth);
      Candidates.swap(NextCandidates);
      if (Candidates.empty())
        break;
    }

#if 1
    if (!Candidates.empty()) {
      for (auto &C : Candidates) {
        errs() << "??? " << C.Cost << '\n';
        printLeaves(Seed, C.Insts);
        break;
      }
      Candidates.resize(1);
    }
#endif
    if (Candidates.empty())
      break;

    for (auto &C : Candidates) {
      ConcreteSeeds.emplace_back();
      auto &S = ConcreteSeeds.back();
      S.insert(S.end(), C.Insts.begin(), C.Insts.end());
    }
    Used = Candidates.front().Used;
  }
}

std::vector<OperandPack> enumerateSeeds(Packer *Pkr, Canonicalizer *Canon,
                                        BasicBlock *BB,
                                        ArrayRef<Canonicalizer::Node *> Nodes) {
  Enumerator E(Pkr, Canon, BB);
  auto AbstractSeeds = E.enumerate(Nodes);

  std::vector<OperandPack> Seeds;
  for (auto &AS : AbstractSeeds) {
    // if (AS.size() != 32) continue;
    E.concretize(Seeds, AS, 32);
  }

  return Seeds;
}
