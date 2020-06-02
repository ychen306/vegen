#include "Solver.h"
#include "MatchManager.h"
#include "llvm/Support/CommandLine.h"

using namespace llvm;

static cl::opt<unsigned> MaxSearchDist(
    "max-search-dist",
    cl::value_desc(
        "Max distance with which we consider two instructions packable."),
    cl::init(20));

Frontier::Frontier(BasicBlock *BB, Packer *Pkr)
    : Pkr(Pkr), BB(BB), VPCtx(Pkr->getContext(BB)), BBIt(BB->rbegin()),
      UnresolvedScalars(VPCtx->getNumValues(), false),
      FreeInsts(VPCtx->getNumValues(), true) {
  // Find external uses of any instruction `I` in `BB`
  // and mark `I` as an unresolved scalar.
  for (auto &I : *BB) {
    for (User *U : I.users()) {
      auto UserInst = dyn_cast<Instruction>(U);
      if (UserInst && UserInst->getParent() != BB) {
        UnresolvedScalars.set(VPCtx->getScalarId(&I));
        break;
      }
    }
  }
}

Instruction *Frontier::getNextFreeInst() const {
  if (BBIt != BB->rend())
    return &*BBIt;
  return nullptr;
}

bool Frontier::hasFreeUser(Value *V) const {
  for (User *U : V->users()) {
    auto *I = dyn_cast<Instruction>(U);
    if (!I || I->getParent() != BB)
      continue;
    if (isFree(I))
      return true;
  }
  return false;
}

namespace {

// Remove elements indexed by `ToRemove`, which is sorted in increasing order.
template <typename T>
void remove(std::vector<T> &X, ArrayRef<unsigned> ToRemove) {
  for (unsigned i : make_range(ToRemove.rbegin(), ToRemove.rend())) {
    std::swap(X[i], X.back());
    X.pop_back();
  }
}

} // namespace

void Frontier::freezeOneInst(unsigned InstId) {
  FreeInsts.reset(InstId);
  UnresolvedScalars.reset(InstId);
}

void Frontier::advanceBBIt() {
  for (auto E = BB->rend(); BBIt != E; ++BBIt)
    if (FreeInsts.test(VPCtx->getScalarId(&*BBIt)))
      break;
}

bool Frontier::resolved(const OperandPack &OP) const {
  for (Value *V : OP) {
    auto *I = dyn_cast<Instruction>(V);
    if (!I || I->getParent() != BB)
      continue;
    if (FreeInsts[VPCtx->getScalarId(V)])
      return false;
  }
  return true;
}

float Frontier::scalarizeFreeUsers(Value *V) {
  if (isa<PHINode>(V))
    return 0;
  float Cost = 0;
  for (User *U : V->users()) {
    auto *I = dyn_cast<Instruction>(U);
    if (!I || I->getParent() != BB || !isFree(I))
      continue;
    Cost += advanceInplace(I, Pkr->getTTI());
  }
  return Cost;
}

float Frontier::advanceInplace(Instruction *I, TargetTransformInfo *TTI) {
  float Cost = scalarizeFreeUsers(I);
  freezeOneInst(VPCtx->getScalarId(I));
  advanceBBIt();

  // Go over unresolved packs and see if we've resolved any lanes
  SmallVector<unsigned, 2> ResolvedPackIds;
  for (unsigned i = 0; i < UnresolvedPacks.size(); i++) {
    auto *OP = UnresolvedPacks[i];
    auto *VecTy = getVectorType(*OP);

    // Special case: we can build OP by broadcasting `I`.
    if (is_splat(*OP) && (*OP)[0] == I) {
      Cost += TTI->getShuffleCost(TargetTransformInfo::SK_Broadcast, VecTy, 0);
      ResolvedPackIds.push_back(i);
      continue;
    }

    // FIXME: Consider the case of *partial* resuse here.
    // E.g. If we have two operand packs (a,b) and (b,a) then we can
    // just explicitly pack (a,b) with insertion and get (b,a) with permutation.
    for (unsigned LaneId = 0; LaneId < OP->size(); LaneId++) {
      if ((*OP)[LaneId] != I)
        continue;
      // Pay the insert cost
      Cost +=
          TTI->getVectorInstrCost(Instruction::InsertElement, VecTy, LaneId);
    }
    if (resolved(*OP))
      ResolvedPackIds.push_back(i);
  }

  // If `I` uses any free instructions,
  // add those to the set of unresolved scalars.
  for (Value *Operand : I->operands()) {
    auto *I2 = dyn_cast<Instruction>(Operand);
    if (!I2 || I2->getParent() != BB)
      continue;
    unsigned InstId = VPCtx->getScalarId(I2);
    if (FreeInsts.test(InstId))
      UnresolvedScalars.set(InstId);
  }

  remove(UnresolvedPacks, ResolvedPackIds);
  std::sort(UnresolvedPacks.begin(), UnresolvedPacks.end());
  return Cost;
}

// Check whether there are lanes in `OpndPack` that are produced by `VP`.
// Also resolve such lanes.
bool Frontier::resolveOperandPack(const VectorPack &VP, const OperandPack &OP) {
  bool Produced = false;
  for (unsigned LaneId = 0; LaneId < OP.size(); LaneId++) {
    auto *V = OP[LaneId];
    auto *I = dyn_cast<Instruction>(V);
    if (!I || I->getParent() != BB)
      continue;
    if (VP.getElements().test(VPCtx->getScalarId(I))) {
      Produced = true;
    }
  }
  return Produced;
}

// Return the cost of gathering from `VP` to `OpndPack`
static unsigned getGatherCost(const VectorPack &VP, const OperandPack &OpndPack,
                              TargetTransformInfo *TTI) {
  if (isConstantPack(OpndPack))
    return 0;

  auto VPVals = VP.getOrderedValues();
  if (VPVals.size() == OpndPack.size()) {
    bool Exact = true;
    for (unsigned i = 0; i < VPVals.size(); i++)
      Exact &= (VPVals[i] == OpndPack[i]);

    // Best case:
    // If `VP` produces `OpndPack` exactly then we don't pay any thing
    if (Exact)
      return 0;

    // Second best case:
    // `VP` produces a permutation of `OpndPack`
    if (std::is_permutation(VPVals.begin(), VPVals.end(), OpndPack.begin()))
      return TTI->getShuffleCost(TargetTransformInfo::SK_PermuteSingleSrc,
                                 getVectorType(VP));
  }

  return 4;
}

// FIXME: this doesn't work when there are lanes in VP that cover multiple
// instructions.
float Frontier::advanceInplace(const VectorPack *VP, TargetTransformInfo *TTI) {
  float Cost = scalarizeFreeUsers(VP);
  Cost += VP->getCost();
  Type *VecTy;
  // It doesn't make sense to get the value type of a store,
  // which returns nothing.
  if (!VP->isStore())
    VecTy = getVectorType(*VP);

  // Tick off instructions taking part in `VP` and pay the scalar extract cost.
  ArrayRef<Value *> OutputLanes = VP->getOrderedValues();
  for (unsigned LaneId = 0; LaneId < OutputLanes.size(); LaneId++) {
    auto *I = cast<Instruction>(OutputLanes[LaneId]);
    unsigned InstId = VPCtx->getScalarId(I);

    // Pay the extract cost
    if (UnresolvedScalars.test(InstId))
      Cost +=
          TTI->getVectorInstrCost(Instruction::ExtractElement, VecTy, LaneId);

    freezeOneInst(InstId);
  }
  advanceBBIt();

  SmallVector<unsigned, 2> ResolvedPackIds;
  if (!VP->isStore()) {
    for (unsigned i = 0; i < UnresolvedPacks.size(); i++) {
      auto *OP = UnresolvedPacks[i];
      if (resolveOperandPack(*VP, *OP)) {
        Cost += getGatherCost(*VP, *OP, TTI);
        if (resolved(*OP))
          ResolvedPackIds.push_back(i);
      }
    }
  }

  // Track the unresolved operand packs used by `VP`
  for (auto *OpndPack : VP->getOperandPacks()) {
    auto *OperandTy = getVectorType(*OpndPack);
    for (unsigned LaneId = 0; LaneId < OpndPack->size(); LaneId++) {
      auto *V = (*OpndPack)[LaneId];
      if (isa<Constant>(V))
        continue;
      auto *I = dyn_cast<Instruction>(V);
      if (!I || I->getParent() != BB) {
        // Assume I is always scalar and pay the insert cost.
        Cost += TTI->getVectorInstrCost(Instruction::InsertElement, OperandTy,
                                        LaneId);
      }
    }
    if (!resolved(*OpndPack) &&
        !std::binary_search(UnresolvedPacks.begin(), UnresolvedPacks.end(),
                            OpndPack))
      UnresolvedPacks.push_back(OpndPack);
  }

  remove(UnresolvedPacks, ResolvedPackIds);
  std::sort(UnresolvedPacks.begin(), UnresolvedPacks.end());
  return Cost;
}

std::unique_ptr<Frontier>
Frontier::advance(const VectorPack *VP, float &Cost,
                  llvm::TargetTransformInfo *TTI) const {
  auto Next = std::make_unique<Frontier>(*this);
  Cost = Next->advanceInplace(VP, TTI);
  return Next;
}

std::unique_ptr<Frontier>
Frontier::advance(llvm::Instruction *I, float &Cost,
                  llvm::TargetTransformInfo *TTI) const {
  auto Next = std::make_unique<Frontier>(*this);
  Cost = Next->advanceInplace(I, TTI);
  std::sort(Next->UnresolvedPacks.begin(), Next->UnresolvedPacks.end());
  return Next;
}

PartialPack::PartialPack(Instruction *Focus, unsigned NumLanes, Packer *Pkr)
    : BB(Focus->getParent()), VPCtx(Pkr->getContext(BB)), Focus(Focus),
      FocusUsed(false), Elements(VPCtx->getNumValues()),
      Depended(VPCtx->getNumValues()), NumLanes(NumLanes), LaneId(0),
      Producer(nullptr), LoadDAG(Pkr->getLoadDAG(BB)),
      StoreDAG(Pkr->getStoreDAG(BB)), LDA(Pkr->getLDA(BB)),
      MM(Pkr->getMatchManager(BB)), TTI(Pkr->getTTI()) {}

PartialPack::PartialPack(Instruction *Focus, const InstBinding *Inst,
                         Packer *Pkr)
    : BB(Focus->getParent()), VPCtx(Pkr->getContext(BB)), Focus(Focus),
      FocusUsed(false), Elements(VPCtx->getNumValues()),
      Depended(VPCtx->getNumValues()), NumLanes(Inst->getLaneOps().size()),
      LaneId(0), Producer(Inst), LoadDAG(Pkr->getLoadDAG(BB)),
      StoreDAG(Pkr->getStoreDAG(BB)), LDA(Pkr->getLDA(BB)),
      MM(Pkr->getMatchManager(BB)), TTI(Pkr->getTTI()) {}

std::vector<Instruction *>
PartialPack::getUsableInsts(const Frontier *Frt) const {
  std::vector<Instruction *> UsableInsts;

  // We can use an instruction if it's independent from the lanes we've filled
  // so far and it's not frozen by `Frt`
  auto IsUsable = [&](Instruction *I) -> bool {
    return 
      !Frt->hasFreeUser(I) &&
      Frt->isFree(I) &&
      checkIndependence(LDA, *VPCtx, I, Elements, Depended);
  };

  // Find out the longest access chain starting from a given instruction
  DenseMap<Instruction *, unsigned> ChainLengths;
  std::function<unsigned(Instruction *, const ConsecutiveAccessDAG &)>
      GetMaxChainLength =
          [&](Instruction *I,
              const ConsecutiveAccessDAG &AccessDAG) -> unsigned {
    if (ChainLengths.count(I))
      return ChainLengths[I];

    auto It = AccessDAG.find(I);
    if (It == AccessDAG.end())
      return (ChainLengths[I] = 1);

    unsigned Longest = 0;
    for (auto *Next : It->second) {
      unsigned Len = GetMaxChainLength(Next, AccessDAG);
      Longest = std::max(Longest, Len);
    }
    return (ChainLengths[I] = Longest);
  };

  bool IsLoad = isa<LoadInst>(Focus);
  bool IsStore = isa<StoreInst>(Focus);
  if (IsLoad || IsStore) {
    const ConsecutiveAccessDAG *AccessDAG;
    if (IsLoad)
      AccessDAG = &LoadDAG;
    else
      AccessDAG = &StoreDAG;
    // For the first lane of a load/store pack, we want to make sure that
    // starting from the the first instruction we can both reach the focus and
    // fill the enough lanes.
    if (LaneId == 0) {
      for (auto &AccessAndNext : *AccessDAG) {
        Instruction *Access = AccessAndNext.first;
        if (GetMaxChainLength(Access, *AccessDAG) >= NumLanes &&
            IsUsable(Access))
          UsableInsts.push_back(Access);
      }
    } else {
      auto *LastAccess = FilledLanes[LaneId - 1];
      auto It = AccessDAG->find(LastAccess);
      if (It == AccessDAG->end())
        return {};
      for (auto *NextAccess : It->second) {
        if (Frt->isFree(NextAccess) && IsUsable(NextAccess))
          UsableInsts.push_back(NextAccess);
      }
    }
  } else {
    assert(Producer);
    // Find all matched operation at a given lane that's also independent
    const Operation *Op = Producer->getLaneOps()[LaneId].getOperation();
    for (auto &M : MM.getMatches(Op)) {
      auto *I = cast<Instruction>(M.Output);
      if (IsUsable(I))
        UsableInsts.push_back(I);
    }
  }

  return UsableInsts;
}

std::unique_ptr<PartialPack>
PartialPack::fillOneLane(llvm::Instruction *I) const {
  auto Next = std::make_unique<PartialPack>(*this);
  Next->Elements.set(VPCtx->getScalarId(I));
  Next->Depended |= LDA.getDepended(I);
  if (auto *LI = dyn_cast<LoadInst>(I))
    Next->Loads.push_back(LI);
  else if (auto *SI = dyn_cast<StoreInst>(I))
    Next->Stores.push_back(SI);
  else {
    const Operation *Op = Producer->getLaneOps()[LaneId].getOperation();
    ArrayRef<Operation::Match> Matches = MM.getMatchesForOutput(Op, I);
    assert(!Matches.empty());
    Next->Matches.push_back(&Matches[0]);
  }

  Next->FocusUsed |= I == Focus;
  ++Next->LaneId;

  return Next;
}

VectorPack *PartialPack::getPack() const {
  if (Elements.count() != NumLanes)
    return nullptr;

  if (isa<LoadInst>(Focus))
    return VPCtx->createLoadPack(Loads, Elements, Depended, TTI);
  else if (isa<StoreInst>(Focus))
    return VPCtx->createStorePack(Stores, Elements, Depended, TTI);
  return VPCtx->createVectorPack(Matches, Elements, Depended, Producer, TTI);
}

class PackEnumerator {
  unsigned MaxNumLanes;
  unsigned EnumCap;
  const VectorPackContext &VPCtx;
  ArrayRef<InstBinding *> Insts;
  const LocalDependenceAnalysis &LDA;
  const ConsecutiveAccessDAG &LoadDAG;
  const ConsecutiveAccessDAG &StoreDAG;
  const MatchManager &MM;
  TargetTransformInfo *TTI;

  bool isUsable(Instruction *I, Instruction *Focus) const {
    return (I == Focus || I->comesBefore(Focus)) &&
           VPCtx.getScalarId(Focus) - VPCtx.getScalarId(I) <= MaxSearchDist;
  }

  void
  enumeratePacksRec(Instruction *Focus, const InstBinding *Inst,
                    const std::vector<ArrayRef<Operation::Match>> &LaneMatches,
                    std::vector<const VectorPack *> &Enumerated,
                    BitVector &Elements, BitVector &Depended,
                    std::vector<const Operation::Match *> &Lanes) const;

  // Find the set of memory accesses that can lead to `FocusAccess`
  // by following the store or load chain
  SmallPtrSet<Instruction *, 16>
  findSeedMemAccesses(Instruction *FocusAccess) const;

  template <typename AccessType>
  VectorPack *createMemAccessPack(ArrayRef<AccessType *> Accesses,
                                  BitVector &Elements, BitVector &Depended,
                                  TargetTransformInfo *) const {
    return nullptr;
  }

  void enumeratePacks(Instruction *Focus,
                      std::vector<const VectorPack *> &Enumerated) const;

  template <typename AccessType>
  void enumerateMemAccesses(AccessType *LI,
                            std::vector<const VectorPack *> &Enumerated) const;

public:
  PackEnumerator(unsigned MaxNumLanes, unsigned EnumCap, BasicBlock *BB,
                 Packer *Pkr)
      : MaxNumLanes(MaxNumLanes), EnumCap(EnumCap), VPCtx(*Pkr->getContext(BB)),
        Insts(Pkr->getInsts()), LDA(Pkr->getLDA(BB)),
        LoadDAG(Pkr->getLoadDAG(BB)), StoreDAG(Pkr->getStoreDAG(BB)),
        MM(Pkr->getMatchManager(BB)), TTI(Pkr->getTTI()) {}

  void enumerate(Instruction *Focus,
                 std::vector<const VectorPack *> &Enumerated) const {
    if (auto *LI = dyn_cast<LoadInst>(Focus))
      enumerateMemAccesses(LI, Enumerated);
    else if (auto *SI = dyn_cast<StoreInst>(Focus))
      enumerateMemAccesses(SI, Enumerated);
    else {
      enumeratePacks(Focus, Enumerated);
    }
  }
};

void PackEnumerator::enumeratePacksRec(
    Instruction *Focus, const InstBinding *Inst,
    const std::vector<ArrayRef<Operation::Match>> &LaneMatches,
    std::vector<const VectorPack *> &Enumerated, BitVector &Elements,
    BitVector &Depended, std::vector<const Operation::Match *> &Lanes) const {
  // The lane we are enumerating
  const unsigned LaneId = Lanes.size();

  auto BackupElements = Elements;
  auto BackupDepended = Depended;

  // Try out all matched operation for this lane.
  Lanes.push_back(nullptr);
  for (auto &Match : LaneMatches[LaneId]) {
    unsigned OutId = VPCtx.getScalarId(Match.Output);
    // Make sure we are allowed to use the matched instruction
    if (!isUsable(cast<Instruction>(Match.Output), Focus))
      continue;
    // Make sure adding this `Match` doesn't violate any dependence constraint
    bool Independent = checkIndependence(
        LDA, VPCtx, cast<Instruction>(Match.Output), Elements, Depended);
    if (!Independent)
      continue;

    // Select this match.
    Elements.set(OutId);
    Depended |= LDA.getDepended(cast<Instruction>(Match.Output));
    Lanes.back() = &Match;

    if (LaneId < LaneMatches.size() - 1) {
      // Recursivly fill out the next lane
      enumeratePacksRec(Focus, Inst, LaneMatches, Enumerated, Elements,
                        Depended, Lanes);
    } else {
      // We've filled the last lane
      Enumerated.push_back(
          VPCtx.createVectorPack(Lanes, Elements, Depended, Inst, TTI));
    }

    // Revert the change before we try out the next match
    Elements = BackupElements;
    Depended = BackupDepended;
    if (Enumerated.size() >= EnumCap)
      break;
  }
  Lanes.pop_back();
}

void PackEnumerator::enumeratePacks(
    Instruction *Focus, std::vector<const VectorPack *> &Enumerated) const {
  for (auto *Inst : Insts) {
    ArrayRef<BoundOperation> LaneOps = Inst->getLaneOps();
    unsigned NumLanes = LaneOps.size();
    if (NumLanes > MaxNumLanes)
      continue;

    // Iterate over all combination of packs, fixing `Focus` at the `i`'th
    // lane
    for (unsigned i = 0; i < NumLanes; i++) {
      std::vector<ArrayRef<Operation::Match>> LaneMatches;
      for (unsigned LaneId = 0; LaneId < NumLanes; LaneId++) {
        ArrayRef<Operation::Match> Matches;
        if (LaneId == i)
          Matches = MM.getMatchesForOutput(LaneOps[i].getOperation(), Focus);
        else
          Matches = MM.getMatches(LaneOps[i].getOperation());

        // if we can't find matches for any given lanes, then we can't use
        // `Inst`
        if (Matches.empty())
          break;
        LaneMatches.push_back(Matches);
      }

      // Skip if we can't find a single match for some lane.
      if (LaneMatches.size() != NumLanes)
        continue;

      std::vector<const Operation::Match *> EmptyPrefix;
      BitVector Elements(VPCtx.getNumValues());
      BitVector Depended(VPCtx.getNumValues());
      enumeratePacksRec(Focus, Inst, LaneMatches, Enumerated, Elements,
                        Depended, EmptyPrefix);
    }
  }
}

SmallPtrSet<Instruction *, 16>
PackEnumerator::findSeedMemAccesses(Instruction *FocusAccess) const {
  DenseSet<Instruction *> Visited;
  SmallPtrSet<Instruction *, 16> Seeds;

  const ConsecutiveAccessDAG *AccessDAG = nullptr;
  if (isa<LoadInst>(FocusAccess))
    AccessDAG = &LoadDAG;
  else if (isa<StoreInst>(FocusAccess))
    AccessDAG = &StoreDAG;

  assert(AccessDAG && "FocusAccess should either be a load or store");

  std::function<bool(Instruction *)> CanReachFocus =
      [&](Instruction *I) -> bool {
    if (I == FocusAccess)
      return true;

    bool Inserted = Visited.insert(I).second;
    if (!Inserted)
      return Seeds.count(I);

    if (!isUsable(I, FocusAccess))
      return false;

    auto It = AccessDAG->find(I);
    // `I` is at the end of the load chain
    if (It == AccessDAG->end())
      return false;

    for (auto *Next : It->second) {
      if (CanReachFocus(Next)) {
        Seeds.insert(I);
        return true;
      }
    }

    return false;
  };

  for (auto &AccessAndNext : *AccessDAG) {
    CanReachFocus(AccessAndNext.first);
  }

  return Seeds;
}

// Explicit specialization for creating load packs
template <>
VectorPack *
PackEnumerator::createMemAccessPack(ArrayRef<LoadInst *> Loads,
                                    BitVector &Elements, BitVector &Depended,
                                    TargetTransformInfo *TTI) const {
  return VPCtx.createLoadPack(Loads, Elements, Depended, TTI);
}

// Explicit specialization for creating store packs
template <>
VectorPack *
PackEnumerator::createMemAccessPack(ArrayRef<StoreInst *> Stores,
                                    BitVector &Elements, BitVector &Depended,
                                    TargetTransformInfo *TTI) const {
  return VPCtx.createStorePack(Stores, Elements, Depended, TTI);
}

template <typename AccessType>
void PackEnumerator::enumerateMemAccesses(
    AccessType *Focus, std::vector<const VectorPack *> &Enumerated) const {
  auto Seeds = findSeedMemAccesses(Focus);

  const ConsecutiveAccessDAG *AccessDAG = nullptr;
  if (std::is_same<AccessType, LoadInst>::value)
    AccessDAG = &LoadDAG;
  else
    AccessDAG = &StoreDAG;

  SmallVector<AccessType *, 8> AccessChain;
  std::function<void(Instruction *, BitVector &&, BitVector &&, bool)>
      EnumerateRec = [&](Instruction *I, BitVector &&Elements,
                         BitVector &&Depended, bool EncounteredFocus) {
        // Include this prefix if we've included the focus.
        if (AccessChain.size() > 1 && EncounteredFocus) {
          Enumerated.push_back(createMemAccessPack<AccessType>(
              AccessChain, Elements, Depended, TTI));
        }
        if (AccessChain.size() >= MaxNumLanes || Enumerated.size() >= EnumCap)
          return;

        // Extend this load chain
        auto It = AccessDAG->find(I);
        if (It == AccessDAG->end())
          return;

        // If the next set of loads contains the focus
        // then we choose that unconditionally.
        if (It->second.count(Focus)) {
          AccessChain.push_back(Focus);
          EncounteredFocus = true;
          // Note that we don't need to update Elements and Depended because
          // they are initialized with `FocusLoad`'s data already.
          EnumerateRec(Focus, std::move(Elements), std::move(Depended),
                       EncounteredFocus);
          AccessChain.pop_back();
          return;
        }

        for (auto *Next : It->second) {
          if (!isUsable(Next, Focus))
            continue;

          bool Independent =
              checkIndependence(LDA, VPCtx, Next, Elements, Depended);
          if (!Independent)
            continue;

          // Include `Next` into the chain of load/store that we will vectorize
          auto ElementsExt = Elements;
          auto DependedExt = Depended;
          AccessChain.push_back(cast<AccessType>(Next));
          ElementsExt.set(VPCtx.getScalarId(Next));
          DependedExt |= LDA.getDepended(Next);
          // Recursively build up the chain
          EnumerateRec(Next, std::move(ElementsExt), std::move(DependedExt),
                       EncounteredFocus);
          AccessChain.pop_back();
        }
      };

  BitVector Elements(VPCtx.getNumValues());
  Elements.set(VPCtx.getScalarId(Focus));
  BitVector Depended = LDA.getDepended(Focus);
  for (auto *Seed : Seeds) {

    if (Seed != Focus) {
      bool Independent =
          checkIndependence(LDA, VPCtx, Seed, Elements, Depended);
      if (!Independent)
        continue;
    }

    auto ElementsExt = Elements;
    auto DependedExt = Depended;
    AccessChain.push_back(cast<AccessType>(Seed));
    ElementsExt.set(VPCtx.getScalarId(Seed));
    DependedExt |= LDA.getDepended(Seed);
    // Recursively build up the load chain
    EnumerateRec(Seed, std::move(ElementsExt), std::move(DependedExt),
                 Seed == Focus);
    AccessChain.pop_back();
  }
}

std::vector<const VectorPack *>
Frontier::filterFrozenPacks(ArrayRef<const VectorPack *> Packs) const {
  BitVector FrozenInsts = FreeInsts;
  FrozenInsts.flip();

  std::vector<const VectorPack *> Filtered;
  Filtered.reserve(Packs.size());
  for (auto *VP : Packs)
    if (!FrozenInsts.anyCommon(VP->getElements()))
      Filtered.push_back(VP);
  return Filtered;
}

std::vector<const VectorPack *>
Frontier::nextAvailablePacks(unsigned MaxNumLanes, unsigned EnumCap,
                             PackEnumerationCache *EnumCache) const {
  Instruction *I = getNextFreeInst();
  bool InCache;
  auto CachedPacks = EnumCache->getPacks(I, InCache);
  if (InCache)
    return filterFrozenPacks(CachedPacks);

  std::vector<const VectorPack *> AvailablePacks;
  PackEnumerator Enumerator(MaxNumLanes, EnumCap, BB, Pkr);

  Enumerator.enumerate(I, AvailablePacks);

  auto Packs = filterFrozenPacks(AvailablePacks);
  EnumCache->insert(I, std::move(AvailablePacks));
  return Packs;
}

// If we already have a UCTNode for the same frontier, reuse that node.
UCTNode *UCTNodeFactory::getNode(std::unique_ptr<Frontier> Frt) {
  //decltype(FrontierToNodeMap)::iterator It;
  //bool Inserted;
  //std::tie(It, Inserted) = FrontierToNodeMap.try_emplace(Frt.get(), nullptr);
  //if (Inserted) {
  //  It->first = Frt.get();
  //  auto *NewNode = new UCTNode(Frt.get());
  //  Nodes.push_back(std::unique_ptr<UCTNode>(NewNode));
  //  It->second = NewNode;
  //  Frontiers.push_back(std::move(Frt));
  //}
  //return It->second;
  auto *NewNode = new UCTNode(Frt.get());
  Nodes.push_back(std::unique_ptr<UCTNode>(NewNode));
  Frontiers.push_back(std::move(Frt));
  return Nodes.back().get();
}

UCTNode *UCTNodeFactory::getNode(const Frontier *Frt,
                                 std::unique_ptr<PartialPack> PP) {
  Nodes.push_back(std::unique_ptr<UCTNode>(new UCTNode(Frt, std::move(PP))));
  return Nodes.back().get();
}

static bool isPartialPackFeasible(const PartialPack &PP, const Frontier *Frt) {
  if (PP.isFilled())
    return true;
  for (auto *I : PP.getUsableInsts(Frt)) {
    std::unique_ptr<PartialPack> PPExtended = PP.fillOneLane(I);
    if (isPartialPackFeasible(*PPExtended, Frt))
      return true;
  }
  return false;
}

// Fill out the children node
void UCTNode::expand(unsigned MaxNumLanes, UCTNodeFactory *Factory,
                     llvm::TargetTransformInfo *TTI) {
  assert(Transitions.empty() && "expanded already");

  if (!PP) {
    // We are not working w/ any partial pack.
    auto *Focus = Frt->getNextFreeInst();

    auto *BB = Frt->getBasicBlock();
    for (auto &I : *BB) {
      if (Frt->hasFreeUser(&I))
        continue;
      if (!Frt->isFree(&I))
        continue;
      float Cost;
      auto *Next = Factory->getNode(Frt->advance(&I, Cost, TTI));
      Transitions.emplace_back(Next, Cost);
    }

    auto *Pkr = getPacker();


    for (auto &I : *BB) {
      auto *Focus = &I;
      if (Frt->hasFreeUser(Focus) || !Frt->isFree(Focus))
        continue;
      // Make a pack that contain the next free inst
      if (auto *LI = dyn_cast<LoadInst>(Focus)) {
        for (unsigned i = 2; i < MaxNumLanes; i++) {
          auto NewPP = std::make_unique<PartialPack>(LI, i, Pkr);
          if (!isPartialPackFeasible(*NewPP, Frt))
            continue;
          Transitions.emplace_back(Factory->getNode(Frt, std::move(NewPP)));
        }
      } else if (auto *SI = dyn_cast<StoreInst>(Focus)) {
        for (unsigned i = 2; i < MaxNumLanes; i++) {
          auto NewPP = std::make_unique<PartialPack>(SI, i, Pkr);
          if (!isPartialPackFeasible(*NewPP, Frt))
            continue;
          Transitions.emplace_back(Factory->getNode(Frt, std::move(NewPP)));
        }
      } else {
        for (auto *Inst : getPacker()->getInsts()) {
          auto NewPP = std::make_unique<PartialPack>(Focus, Inst, Pkr);
          if (!isPartialPackFeasible(*NewPP, Frt))
            continue;
          Transitions.emplace_back(Factory->getNode(Frt, std::move(NewPP)));
        }
      }
    }
  } else {
    // We are filling out a partial pack
    std::vector<Instruction *> UsableInsts = PP->getUsableInsts(Frt);

    assert(!UsableInsts.empty());

    for (auto *I : UsableInsts) {
      std::unique_ptr<PartialPack> NextPP = PP->fillOneLane(I);
      if (!isPartialPackFeasible(*NextPP, Frt))
        continue;
      if (auto *VP = NextPP->getPack()) {
        // Finished filling out this pack; move to the next frontier.
        float Cost;
        std::unique_ptr<Frontier> NextFrt = Frt->advance(VP, Cost, TTI);
        // If the focus is not used, additionally make the focus scalar.
        if (!NextPP->focusUsed()) {
          float Cost2;
          NextFrt = NextFrt->advance(Frt->getNextFreeInst(), Cost2, TTI);
          Cost += Cost2;
        }
        Transitions.emplace_back(VP, Factory->getNode(std::move(NextFrt)),
                                 Cost);
      } else {
        Transitions.emplace_back(Factory->getNode(Frt, std::move(NextPP)));
      }
    }
  }
}

// Do one iteration of MCTS
void UCTSearch::run(UCTNode *Root, unsigned NumIters) {
  struct FullTransition {
    UCTNode *Parent;
    UCTNode::Transition *T;
  };

  std::vector<FullTransition> Path;
  for (int Iter = 0; Iter < (int)NumIters; Iter++) {
    Path.clear();

    // ========= 1) Selection ==========
    UCTNode *CurNode = Root;

    // Traverse down to a leaf node.
    while (CurNode->expanded()) {
      auto &Transitions = CurNode->transitions();
      // Transition weight given by some prior predictor (i.e., the apprentice)
      auto TransitionWeight = CurNode->transitionWeight();
      bool HasPredictions = TransitionWeight.size() > 0;

      auto ScoreTransition = [&](unsigned i) -> float {
        auto &T = Transitions[i];
        float Score = CurNode->score(T, C);
        if (HasPredictions)
          Score += W * TransitionWeight[i] / (float)(T.visitCount() + 1);
        return Score;
      };

      UCTNode::Transition *BestT = &Transitions[0];
      float MaxUCTScore = 0;
      if (BestT->visited())
        MaxUCTScore = ScoreTransition(0);

      for (unsigned i = 0; i < Transitions.size(); i++) {
        auto &T = Transitions[i];
        if (!T.visited()) {
          BestT = &T;
          break;
        }

        float UCTScore = ScoreTransition(i);
        if (UCTScore > MaxUCTScore) {
          MaxUCTScore = UCTScore;
          BestT = &T;
        }
      }

      Path.push_back(FullTransition{CurNode, BestT});
      CurNode = BestT->Next;
    }

    float LeafCost = 0;
    // ========= 2) Expansion ==========
    if (!CurNode->isTerminal()) {
      // ======= 3) Evaluation/Simulation =======
      LeafCost = evalLeafNode(CurNode);
      if (CurNode->visitCount() >= ExpandThreshold) {
        // FIXME: make max num lanes a parameter of MCTS ctor
        CurNode->expand(Policy ? Policy->getMaxNumLanes() : 8, Factory, TTI);
        auto &Transitions = CurNode->transitions();
        // Bias future exploration on this node if there is a prior
        if (Policy && Transitions.size() > 1)
          Policy->predictAsync(CurNode);
      }
    }

    // ========= 4) Backpropagation ===========
    CurNode->update(LeafCost);
    float TotalCost = LeafCost;
    for (FullTransition &FT : make_range(Path.rbegin(), Path.rend())) {
      TotalCost += FT.T->Cost;
      FT.Parent->update(TotalCost);
      FT.T->Count += 1;
    }
  }
}

// Uniformly random rollout
float RolloutEvaluator::evaluate(unsigned MaxNumLanes, unsigned EnumCap,
                                 const Frontier *Frt, const PartialPack *PP,
                                 PackEnumerationCache &EnumCache, Packer *Pkr) {
  Frontier FrtScratch = *Frt;
  BasicBlock *BB = Frt->getBasicBlock();
  float Cost = 0;
  auto *TTI = Pkr->getTTI();
  auto &MM = Pkr->getMatchManager(BB);
  auto *VPCtx = Pkr->getContext(BB);
  auto &LDA = Pkr->getLDA(BB);
  auto &LoadDAG = Pkr->getLoadDAG(BB);
  
  // If we are still filling out a partial pack,
  // use do a random rollout to fill out the partial pack.
  if (PP) {
    std::unique_ptr<PartialPack> PPScratch;
    for (;;) {
      auto UsableInsts = PP->getUsableInsts(Frt);
      assert(!UsableInsts.empty());
      std::vector<std::unique_ptr<PartialPack>> NextPPs;
      for (auto *I : UsableInsts) {
        auto NextPP = PP->fillOneLane(I);
        if (isPartialPackFeasible(*NextPP, Frt))
          NextPPs.push_back(std::move(NextPP));
      }
      PPScratch = std::move(NextPPs[rand_int(NextPPs.size())]);
      auto *VP = PPScratch->getPack();
      if (VP) {
        Cost += FrtScratch.advanceInplace(VP, TTI);
        break;
      }
      PP = PPScratch.get();
    }
  }


  for (;;) {
    auto *I = FrtScratch.getNextFreeInst();
    if (!I)
      break;

    std::vector<VectorPack *> Extensions;
    for (auto *OP : FrtScratch.getUnresolvedPacks()) {
      unsigned NumLanes = OP->size();
      BitVector Elements(VPCtx->getNumValues());
      BitVector Depended(VPCtx->getNumValues());
      bool Extendable = true;
      bool AllLoads = true;
      for (unsigned i = 0; i < NumLanes; i++) {
        auto *V = (*OP)[i];
        auto *I = dyn_cast<Instruction>(V);
        if (!I || I->getParent() != BB || !FrtScratch.isFree(I)) {
          Extendable = false;
          break;
        }
        unsigned InstId = VPCtx->getScalarId(I);
        if (!checkIndependence(LDA, *VPCtx, I, Elements, Depended)) {
          Extendable = false;
          break;
        }
        if (!isa<LoadInst>(I))
          AllLoads = false;
        Elements.set(InstId);
        Depended |= LDA.getDepended(I);
      }

      if (!Extendable)
        continue;

      if (AllLoads) {
        // Simply pack all of the loads if they are consecutive.
        bool Consecutive = true;
        std::vector<LoadInst *> Loads { cast<LoadInst>((*OP)[0]) };
        for (unsigned i = 1; i < NumLanes; i++) {
          auto *CurLoad = cast<LoadInst>((*OP)[i]);
          auto *PrevLoad = cast<LoadInst>((*OP)[i-1]);
          auto It = LoadDAG.find(PrevLoad);
          if (It == LoadDAG.end() || !It->second.count(CurLoad)) {
            Consecutive = false;
            break;
          }
          Loads.push_back(CurLoad);
        }
        if (Consecutive)
          Extensions.push_back(VPCtx->createLoadPack(Loads, Elements, Depended, TTI));
      }

      for (auto *Inst : Pkr->getInsts()) {
        ArrayRef<BoundOperation> LaneOps = Inst->getLaneOps();
        if (LaneOps.size() != NumLanes)
          continue;

        std::vector<const Operation::Match *> Lanes;
        for (unsigned i = 0; i < NumLanes; i++) {
          auto *I = cast<Instruction>((*OP)[i]);
           ArrayRef<Operation::Match> Matches =
             MM.getMatchesForOutput(LaneOps[i].getOperation(), I);
           if (Matches.empty())
             break;
           // FIXME: consider multiple matches for the same operation
           Lanes.push_back(&Matches[0]);
        }
        
        if (Lanes.size() == NumLanes) {
          Extensions.push_back(VPCtx->createVectorPack(Lanes, Elements, Depended, Inst, TTI));
          break;
        }
      }
    }

    if (!Extensions.empty()) {
      auto *VP = Extensions[rand_int(Extensions.size())];
      Cost += FrtScratch.advanceInplace(VP, TTI);
    } else {
      Cost += FrtScratch.advanceInplace(I, TTI);
    }
    if (FrtScratch.getUnresolvedPacks().empty() && FrtScratch.numUnresolvedScalars() == 0)
      break;
  }
  return Cost;
}
