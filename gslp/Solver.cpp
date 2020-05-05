#include "Solver.h"
#include "MatchManager.h"

using namespace llvm;

Frontier::Frontier(BasicBlock *BB, const VectorPackContext *VPCtx)
    : BB(BB), VPCtx(VPCtx), BBIt(BB->rbegin()),
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

namespace {

template <typename T>
void remove(std::vector<T> &X, ArrayRef<unsigned> ToRemove) {
  for (unsigned i : ToRemove) {
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
    auto *I = cast<Instruction>(V);
    if (!I || I->getParent() != BB)
      continue;
    if (FreeInsts[VPCtx->getScalarId(V)])
      return false;
  }
  return true;
}

float Frontier::advanceInplace(Instruction *I, TargetTransformInfo *TTI) {
  freezeOneInst(VPCtx->getScalarId(I));
  advanceBBIt();

  // Go over unresolved packs and see if we've resolved any lanes
  float Cost = 0;
  SmallVector<unsigned, 2> ResolvedPackIds;
  for (unsigned i = 0; i < UnresolvedPacks.size(); i++) {
    auto *OP = UnresolvedPacks[i];
    auto *VecTy = getVectorType(*OP);

    // Special case: we can build OP by broadcasting `I`.
    if (is_splat(*OP)) {
      Cost += TTI->getShuffleCost(TargetTransformInfo::SK_Broadcast, VecTy, 0);
      ResolvedPackIds.push_back(i);
      continue;
    }

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
  float Cost = VP->getCost();
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
        Cost += TTI->getVectorInstrCost(Instruction::ExtractElement, OperandTy,
                                        LaneId);
      }
    }
    if (!resolved(*OpndPack) &&
        !std::binary_search(UnresolvedPacks.begin(), UnresolvedPacks.end(),
                            OpndPack))
      UnresolvedPacks.push_back(OpndPack);
  }

  remove(UnresolvedPacks, ResolvedPackIds);
  return Cost;
}

std::unique_ptr<Frontier>
Frontier::advance(const VectorPack *VP, float &Cost,
                  llvm::TargetTransformInfo *TTI) const {
  auto Next = std::make_unique<Frontier>(*this);
  Cost = Next->advanceInplace(VP, TTI);
  std::sort(Next->UnresolvedPacks.begin(), Next->UnresolvedPacks.end());
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

class PackEnumerator {
  const VectorPackContext &VPCtx;
  ArrayRef<InstBinding *> Insts;
  const LocalDependenceAnalysis &LDA;
  const ConsecutiveAccessDAG &LoadDAG;
  const ConsecutiveAccessDAG &StoreDAG;
  const MatchManager &MM;
  TargetTransformInfo *TTI;

  bool isFree(Instruction *I, Instruction *Focus) const {
    return I == Focus || I->comesBefore(Focus);
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
  PackEnumerator(BasicBlock *BB, Packer *Pkr)
      : VPCtx(*Pkr->getContext(BB)), Insts(Pkr->getInsts()),
        LDA(Pkr->getLDA(BB)), LoadDAG(Pkr->getLoadDAG(BB)),
        StoreDAG(Pkr->getStoreDAG(BB)), MM(Pkr->getMatchManager(BB)),
        TTI(Pkr->getTTI()) {}

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

  // Try out all matched operation for this line
  Lanes.push_back(nullptr);
  for (auto &Match : LaneMatches[LaneId]) {
    unsigned OutId = VPCtx.getScalarId(Match.Output);
    // Make sure we are allowed to use the matched instruction
    if (!isFree(cast<Instruction>(Match.Output), Focus))
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
  }
  Lanes.pop_back();
}

void PackEnumerator::enumeratePacks(
    Instruction *Focus, std::vector<const VectorPack *> &Enumerated) const {
  for (auto *Inst : Insts) {
    ArrayRef<BoundOperation> LaneOps = Inst->getLaneOps();
    unsigned NumLanes = LaneOps.size();
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

    if (!isFree(I, FocusAccess))
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
        if (AccessChain.size() > 8)
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
          if (!isFree(Next, Focus))
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
Frontier::nextAvailablePacks(Packer *Pkr,
                             PackEnumerationCache *EnumCache) const {
  Instruction *I = getNextFreeInst();
  bool InCache;
  auto CachedPacks = EnumCache->getPacks(I, InCache);
  if (InCache)
    return filterFrozenPacks(CachedPacks);

  std::vector<const VectorPack *> AvailablePacks;
  PackEnumerator Enumerator(BB, Pkr);

  Enumerator.enumerate(I, AvailablePacks);

  auto Packs = filterFrozenPacks(AvailablePacks);
  EnumCache->insert(I, std::move(AvailablePacks));
  return Packs;
}

// If we already have a UCTNode for the same frontier, reuse that node.
UCTNode *UCTNodeFactory::getNode(std::unique_ptr<Frontier> Frt) {
  decltype(FrontierToNodeMap)::iterator It;
  bool Inserted;
  std::tie(It, Inserted) = FrontierToNodeMap.try_emplace(Frt.get(), nullptr);
  if (Inserted) {
    It->first = Frt.get();
    auto *NewNode = new UCTNode(Frt.get());
    Nodes.push_back(std::unique_ptr<UCTNode>(NewNode));
    It->second = NewNode;
    Frontiers.push_back(std::move(Frt));
  }
  return It->second;
}

// Fill out the children node
void UCTNode::expand(UCTNodeFactory *Factory, Packer *Pkr,
                     PackEnumerationCache *EnumCache,
                     llvm::TargetTransformInfo *TTI) {
  assert(Transitions.empty() && "expanded already");
  float Cost;

  // Consider keeping the next free inst scalar
  auto *Next =
      Factory->getNode(Frt->advance(Frt->getNextFreeInst(), Cost, TTI));
  Transitions.emplace_back(nullptr, Next, Cost);

  auto AvailablePacks = Frt->nextAvailablePacks(Pkr, EnumCache);

  Transitions.reserve(AvailablePacks.size());
  for (auto *VP : AvailablePacks) {
    auto *Next = Factory->getNode(Frt->advance(VP, Cost, TTI));
    Transitions.emplace_back(VP, Next, Cost);
  }
}

// Do one iteration of MCTS
void UCTSearch::run(UCTNode *Root, unsigned Iter) {
  struct FullTransition {
    UCTNode *Parent;
    UCTNode::Transition *T;
  };

  std::vector<FullTransition> Path;
  std::vector<float> Weight; // Weights given by a prior policy
  while (Iter--) {
    errs() << "!!! " << Iter << '\n';
    Path.clear();

    // ========= 1) Selection ==========
    UCTNode *CurNode = Root;

    // Traverse down to a leaf node.
    while (CurNode->expanded()) {
      auto &Transitions = CurNode->transitions();
      if (Policy)
        Policy->predict(CurNode->getFrontier(), Transitions, Pkr, Weight);

      unsigned VisitCount = CurNode->visitCount();
      auto ScoreTransition = [&](unsigned i) -> float {
        float Score = Transitions[i].score(VisitCount, C);
        if (Policy)
          Score += Weight[i];
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
      CurNode->expand(Factory, Pkr, &EnumCache, TTI);
    }

    // ========= 4) Backpropagation ===========
    CurNode->update(LeafCost);
    float TotalCost = LeafCost;
    for (FullTransition &FT : make_range(Path.rbegin(), Path.rend())) {
      TotalCost += FT.T->Cost;
      FT.Parent->update(TotalCost);
      FT.T->Count += 1;
    }

    if (TotalCost < 0)
      errs() << "Total Cost: " << TotalCost << '\n';
  }
}

// Uniformly random rollout
float RolloutEvaluator::evaluate(const Frontier *Frt,
                                 PackEnumerationCache &EnumCache, Packer *Pkr) {
  Frontier FrtScratch = *Frt;
  float Cost = 0;
  PackEnumerator Enumerator(Frt->getBasicBlock(), Pkr);
  auto *TTI = Pkr->getTTI();

  auto sampleFromPack = [&FrtScratch,
                         TTI](Instruction *I,
                              ArrayRef<const VectorPack *> Packs) -> float {
    auto FrozenInsts = FrtScratch.getFreeInsts();
    FrozenInsts.flip();

    for (;;) {
      unsigned PackId = rand_int(Packs.size() + 1);
      if (PackId == 0) // go with scalar
        return FrtScratch.advanceInplace(I, TTI);
      else {
        auto *VP = Packs[PackId - 1];
        if (!FrozenInsts.anyCommon(VP->getElements()))
          return FrtScratch.advanceInplace(VP, TTI);
      }
    }
  };

  for (;;) {
    auto *I = FrtScratch.getNextFreeInst();
    if (!I)
      break;
    // auto Packs = FrtScratch.nextAvailablePacks(Pkr, &EnumCache);
    bool InCache;
    auto CachedPacks = EnumCache.getPacks(I, InCache);
    if (InCache)
      Cost += sampleFromPack(I, CachedPacks);
    else {
      std::vector<const VectorPack *> Packs;
      Enumerator.enumerate(I, Packs);
      Cost += sampleFromPack(I, Packs);
      EnumCache.insert(I, std::move(Packs));
    }
  }
  return Cost;
}
