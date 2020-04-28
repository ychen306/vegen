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

std::unique_ptr<Frontier> Frontier::advance(Instruction *I, float &Cost,
                                            TargetTransformInfo *TTI) const {
  auto Next = std::make_unique<Frontier>(*this);

  Next->freezeOneInst(VPCtx->getScalarId(I));
  Next->advanceBBIt();

  // Go over unresolved packs and see if we've resolved any lanes
  Cost = 0;
  SmallVector<unsigned, 2> ResolvedPackIds;
  for (unsigned i = 0; i < Next->UnresolvedPacks.size(); i++) {
    auto *OP = Next->UnresolvedPacks[i];
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
    if (Next->resolved(*OP))
      ResolvedPackIds.push_back(i);
  }

  // If `I` uses any free instructions,
  // add those to the set of unresolved scalars.
  for (Value *Operand : I->operands()) {
    auto *I2 = dyn_cast<Instruction>(Operand);
    if (!I2 || I2->getParent() != BB)
      continue;
    unsigned InstId = VPCtx->getScalarId(I2);
    if (Next->FreeInsts.test(InstId))
      Next->UnresolvedScalars.set(InstId);
  }

  remove(Next->UnresolvedPacks, ResolvedPackIds);
  std::sort(Next->UnresolvedPacks.begin(), Next->UnresolvedPacks.end());

  return Next;
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

  return 2;
}

// FIXME: this doesn't work when there are lanes in VP that cover multiple
// instructions.
std::unique_ptr<Frontier> Frontier::advance(const VectorPack *VP, float &Cost,
                                            TargetTransformInfo *TTI) const {
  auto Next = std::make_unique<Frontier>(*this);

  Cost = VP->getCost();
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
    if (Next->UnresolvedScalars.test(InstId))
      Cost +=
          TTI->getVectorInstrCost(Instruction::ExtractElement, VecTy, LaneId);

    Next->freezeOneInst(InstId);
  }
  Next->advanceBBIt();

  SmallVector<unsigned, 2> ResolvedPackIds;
  if (!VP->isStore()) {
    for (unsigned i = 0; i < Next->UnresolvedPacks.size(); i++) {
      auto *OP = Next->UnresolvedPacks[i];
      if (bool PartiallyResolved = Next->resolveOperandPack(*VP, *OP)) {
        Cost += getGatherCost(*VP, *OP, TTI);
        if (Next->resolved(*OP))
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

    if (!Next->resolved(*OpndPack))
      Next->UnresolvedPacks.push_back(OpndPack);
  }

  remove(Next->UnresolvedPacks, ResolvedPackIds);
  std::sort(Next->UnresolvedPacks.begin(), Next->UnresolvedPacks.end());

  return Next;
}

class PackEnumerator {
  Instruction *Focus;
  const VectorPackContext &VPCtx;
  const LocalDependenceAnalysis &LDA;
  const ConsecutiveAccessDAG &LoadDAG;
  const ConsecutiveAccessDAG &StoreDAG;
  TargetTransformInfo *TTI;

  bool isFree(Instruction *I) const {
    return I == Focus || I->comesBefore(Focus);
  }

  void
  enumeratePacksRec(const InstBinding *Inst,
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

public:
  PackEnumerator(Instruction *Focus, const VectorPackContext &VPCtx,
                 const LocalDependenceAnalysis &LDA,
                 const ConsecutiveAccessDAG &LoadDAG,
                 const ConsecutiveAccessDAG &StoreDAG, TargetTransformInfo *TTI)
      : Focus(Focus), VPCtx(VPCtx), LDA(LDA), LoadDAG(LoadDAG),
        StoreDAG(StoreDAG), TTI(TTI) {}
  void
  enumeratePacks(const InstBinding *Inst,
                 const std::vector<ArrayRef<Operation::Match>> &LaneMatches,
                 std::vector<const VectorPack *> &Enumerated) const {
    std::vector<const Operation::Match *> EmptyPrefix;
    BitVector Elements(VPCtx.getNumValues());
    BitVector Depended(VPCtx.getNumValues());
    enumeratePacksRec(Inst, LaneMatches, Enumerated, Elements, Depended,
                      EmptyPrefix);
  }

  template <typename AccessType>
  void enumerateMemAccesses(AccessType *LI,
                            std::vector<const VectorPack *> &Enumerated) const;
};

void PackEnumerator::enumeratePacksRec(
    const InstBinding *Inst,
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
    if (!isFree(cast<Instruction>(Match.Output)))
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
      enumeratePacksRec(Inst, LaneMatches, Enumerated, Elements, Depended,
                        Lanes);
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

    if (!isFree(I))
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
          if (!isFree(Next))
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

  ArrayRef<InstBinding *> Insts = Pkr->getInsts();
  auto &MM = Pkr->getMatchManager(BB);
  auto &LDA = Pkr->getLDA(BB);
  auto &LoadDAG = Pkr->getLoadDAG(BB);
  auto &StoreDAG = Pkr->getStoreDAG(BB);
  auto *TTI = Pkr->getTTI();

  std::vector<const VectorPack *> AvailablePacks;
  PackEnumerator Enumerator(I, *VPCtx, LDA, LoadDAG, StoreDAG, TTI);

  if (auto *LI = dyn_cast<LoadInst>(I))
    Enumerator.enumerateMemAccesses(LI, AvailablePacks);
  else if (auto *SI = dyn_cast<StoreInst>(I))
    Enumerator.enumerateMemAccesses(SI, AvailablePacks);
  else {
    for (auto *Inst : Insts) {
      ArrayRef<BoundOperation> LaneOps = Inst->getLaneOps();
      unsigned NumLanes = LaneOps.size();
      // Iterate over all combination of packs, fixing `I` at the `i`'th lane
      for (unsigned i = 0; i < NumLanes; i++) {
        std::vector<ArrayRef<Operation::Match>> LaneMatches;
        for (unsigned LaneId = 0; LaneId < NumLanes; LaneId++) {
          ArrayRef<Operation::Match> Matches;
          if (LaneId == i)
            Matches = MM.getMatchesForOutput(LaneOps[i].getOperation(), I);
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
        Enumerator.enumeratePacks(Inst, LaneMatches, AvailablePacks);
      }
    }
  }

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
  assert(OutEdges.empty() && "expanded already");
  float Cost;

  // Consider keeping the next free inst scalar
  auto *Next =
      Factory->getNode(Frt->advance(Frt->getNextFreeInst(), Cost, TTI));
  OutEdges.push_back(OutEdge{nullptr, Next, Cost});

  auto AvailablePacks = Frt->nextAvailablePacks(Pkr, EnumCache);

  OutEdges.reserve(AvailablePacks.size());
  for (auto *VP : AvailablePacks) {
    auto *Next = Factory->getNode(Frt->advance(VP, Cost, TTI));
    OutEdges.push_back(OutEdge{VP, Next, Cost});
  }
}

// Do one iteration of MCTS
void UCTSearch::run(UCTNode *Root, unsigned Iter) {
  std::vector<const UCTNode::OutEdge *> Path;
  while (Iter--) {
    Path.clear();

    // ========= 1) Selection ==========
    UCTNode *CurNode = Root;

    // Traverse down to a leaf node.
    while (CurNode->expanded()) {
      // Compare out-going edges by UCT score
      unsigned VisitCount = CurNode->visitCount();
      auto compareEdge = [VisitCount, this](const UCTNode::OutEdge &A,
                                            const UCTNode::OutEdge &B) {
        // If we haven't visited the dest of A, then give it infinite weight
        if (A.Next->visitCount() == 0)
          return false;
        // If we haven't visited the dest of B ...
        if (B.Next->visitCount() == 0)
          return true;

        return -A.Cost + A.Next->score(VisitCount, C) <
               -B.Cost + B.Next->score(VisitCount, C);
      };

      auto OutEdges = CurNode->next();

      // Select the node maximizing the UCT formula
      auto It = std::max_element(OutEdges.begin(), OutEdges.end(), compareEdge);
      Path.push_back(&*It);
      CurNode = It->Next;
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
    for (int i = Path.size() - 2; i >= 0; i--) {
      auto *Edge = Path[i];
      TotalCost += Path[i + 1]->Cost;
      Edge->Next->update(TotalCost);
    }
  }
}
