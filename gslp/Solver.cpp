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
      FreeInsts(VPCtx->getNumValues(), true),
      UsableInsts(VPCtx->getNumValues(), false) {
  // Find external uses of any instruction `I` in `BB`
  // and mark `I` as an unresolved scalar.
  for (auto &I : *BB) {
    bool AllUsersResolved = true;
    unsigned InstId = VPCtx->getScalarId(&I);
    for (User *U : I.users()) {
      auto UserInst = dyn_cast<Instruction>(U);
      if (UserInst && UserInst->getParent() != BB) {
        UnresolvedScalars.set(InstId);
      } else if (UserInst) {
        AllUsersResolved = false;
      }
    }

    if (AllUsersResolved || isa<PHINode>(&I))
      UsableInsts.set(InstId);
  }
}

Instruction *Frontier::getNextFreeInst() const {
  if (BBIt != BB->rend())
    return &*BBIt;
  return nullptr;
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

void Frontier::freezeOneInst(Instruction *I) {
  unsigned InstId = VPCtx->getScalarId(I);
  FreeInsts.reset(InstId);
  UnresolvedScalars.reset(InstId);
  UsableInsts.reset(InstId);

  // See if freezing `I` makes any of its operands *usable*
  for (Value *Operand : I->operands()) {
    auto OI = dyn_cast<Instruction>(Operand);
    if (!OI || OI->getParent() != BB)
      continue;

    bool Usable = true;
    // An instruction is usable if all of its users are frozen
    for (User *U : OI->users()) {
      auto *UserInst = dyn_cast<Instruction>(U);
      if (UserInst && UserInst->getParent() == BB && isFree(UserInst)) {
        Usable = false;
        break;
      }
    }
    if (Usable)
      UsableInsts.set(VPCtx->getScalarId(OI));
  }
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

float Frontier::advanceInplace(Instruction *I, TargetTransformInfo *TTI) {
  float Cost = 0;
  freezeOneInst(I);
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

    freezeOneInst(I);
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

PartialPack::PartialPack(bool IsLoad, bool IsStore, BasicBlock *BB, unsigned NumLanes, Packer *Pkr)
    : IsLoad(IsLoad), IsStore(IsStore), BB(BB),
      VPCtx(Pkr->getContext(BB)),
      Elements(VPCtx->getNumValues()),
      Depended(VPCtx->getNumValues()), NumLanes(NumLanes), LaneId(0),
      Producer(nullptr), LoadDAG(Pkr->getLoadDAG(BB)),
      StoreDAG(Pkr->getStoreDAG(BB)), LDA(Pkr->getLDA(BB)),
      MM(Pkr->getMatchManager(BB)), TTI(Pkr->getTTI()) {}

PartialPack::PartialPack(const InstBinding *Inst, BasicBlock *BB, Packer *Pkr)
    : IsLoad(false), IsStore(false),
      BB(BB), VPCtx(Pkr->getContext(BB)),
      Elements(VPCtx->getNumValues()),
      Depended(VPCtx->getNumValues()), NumLanes(Inst->getLaneOps().size()),
      LaneId(0), Producer(Inst), LoadDAG(Pkr->getLoadDAG(BB)),
      StoreDAG(Pkr->getStoreDAG(BB)), LDA(Pkr->getLDA(BB)),
      MM(Pkr->getMatchManager(BB)), TTI(Pkr->getTTI()) {}


std::vector<Instruction *>
PartialPack::getUsableInsts(const Frontier *Frt) const {
  assert(!isFilled());
  std::vector<Instruction *> UsableInsts;

  auto IsUsable = [&](Instruction *I) -> bool {
    return Frt->isUsable(I) &&
      checkIndependence(LDA, *VPCtx, I, Elements, Depended);
  };

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
        auto *Access = AccessAndNext.first;
        if (IsUsable(Access))
          UsableInsts.push_back(Access);
      }
    } else {
      auto *LastAccess = FilledLanes[LaneId - 1];
      auto It = AccessDAG->find(LastAccess);
      if (It == AccessDAG->end()) {
        return {};
      }
      for (auto *NextAccess : It->second) {
        if (IsUsable(NextAccess))
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

std::unique_ptr<PartialPack> PartialPack::fillOneLane(Instruction *I) const {
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
  Next->FilledLanes.push_back(I);
  ++Next->LaneId;

  return Next;
}

VectorPack *PartialPack::getPack() const {
  if (Elements.count() != NumLanes)
    return nullptr;

  if (IsLoad) {
    return VPCtx->createLoadPack(Loads, Elements, Depended, TTI);
  } else if (IsStore)
    return VPCtx->createStorePack(Stores, Elements, Depended, TTI);
  return VPCtx->createVectorPack(Matches, Elements, Depended, Producer, TTI);
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
  // auto *NewNode = new UCTNode(Frt.get());
  // Nodes.push_back(std::unique_ptr<UCTNode>(NewNode));
  // Frontiers.push_back(std::move(Frt));
  // return Nodes.back().get();
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
    if (isPartialPackFeasible(*PPExtended, Frt)) {
      return true;
    }
  }
  return false;
}

static std::vector<const VectorPack *> findExtensionPacks(const Frontier &Frt) {
  auto *Pkr = Frt.getPacker();
  auto *BB = Frt.getBasicBlock();
  auto &LDA = Pkr->getLDA(BB);
  auto *VPCtx = Pkr->getContext(BB);
  auto *TTI = Pkr->getTTI();
  auto &LoadDAG = Pkr->getLoadDAG(BB);
  auto &MM = Pkr->getMatchManager(BB);

  std::vector<const VectorPack *> Extensions;
  for (auto *OP : Frt.getUnresolvedPacks()) {
    unsigned NumLanes = OP->size();
    BitVector Elements(VPCtx->getNumValues());
    BitVector Depended(VPCtx->getNumValues());
    bool Extensible = true;
    bool AllLoads = true;
    for (unsigned i = 0; i < NumLanes; i++) {
      auto *V = (*OP)[i];
      auto *I = dyn_cast<Instruction>(V);
      if (!I || I->getParent() != BB || !Frt.isUsable(I)) {
        Extensible = false;
        break;
      }
      unsigned InstId = VPCtx->getScalarId(I);
      if (!checkIndependence(LDA, *VPCtx, I, Elements, Depended)) {
        Extensible = false;
        break;
      }
      if (!isa<LoadInst>(I))
        AllLoads = false;
      Elements.set(InstId);
      Depended |= LDA.getDepended(I);
    }

    if (!Extensible)
      continue;

    if (AllLoads) {
      // Simply pack all of the loads if they are consecutive.
      bool Consecutive = true;
      std::vector<LoadInst *> Loads{cast<LoadInst>((*OP)[0])};
      for (unsigned i = 1; i < NumLanes; i++) {
        auto *CurLoad = cast<LoadInst>((*OP)[i]);
        auto *PrevLoad = cast<LoadInst>((*OP)[i - 1]);
        auto It = LoadDAG.find(PrevLoad);
        if (It == LoadDAG.end() || !It->second.count(CurLoad)) {
          Consecutive = false;
          break;
        }
        Loads.push_back(CurLoad);
      }
      if (Consecutive)
        Extensions.push_back(
            VPCtx->createLoadPack(Loads, Elements, Depended, TTI));
      continue;
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
        Extensions.push_back(
            VPCtx->createVectorPack(Lanes, Elements, Depended, Inst, TTI));
        break;
      }
    }
  }
  return Extensions;
}


// Fill out the children node
void UCTNode::expand(unsigned MaxNumLanes, UCTNodeFactory *Factory,
                     llvm::TargetTransformInfo *TTI) {
  assert(Transitions.empty() && "expanded already");
  auto *Pkr = getPacker();

  if (!PP) {
    // We are not working w/ any partial pack, start partial packs!
    auto *BB = Frt->getBasicBlock();
    for (auto *V : Frt->usableInsts()) {
      auto *I = cast<Instruction>(V);
      float Cost;
      auto *Next = Factory->getNode(Frt->advance(I, Cost, TTI));
      Transitions.emplace_back(Next, Cost);
    }

    //// Also consider the extension packs
    //std::vector<const VectorPack *> Extensions = findExtensionPacks(*Frt);
    //for (auto *VP : Extensions) {
    //  float Cost;
    //  auto *Next = Factory->getNode(Frt->advance(VP, Cost, TTI));
    //  Transitions.emplace_back(VP, Next, Cost);
    //}

    static std::vector<unsigned> VL{2, 4, 8};
    // Make a pack that contain the next free inst
    for (unsigned i : VL) {
      auto NewPP = std::make_unique<PartialPack>(true, false, BB, i, Pkr);
      if (isPartialPackFeasible(*NewPP, Frt))
        Transitions.emplace_back(Factory->getNode(Frt, std::move(NewPP)));
    }
    for (unsigned i : VL) {
      auto NewPP = std::make_unique<PartialPack>(false, true, BB, i, Pkr);
      if (isPartialPackFeasible(*NewPP, Frt))
        Transitions.emplace_back(Factory->getNode(Frt, std::move(NewPP)));
    }
    for (auto *Inst : getPacker()->getInsts()) {
      auto NewPP = std::make_unique<PartialPack>(Inst, BB, Pkr);
      if (isPartialPackFeasible(*NewPP, Frt)) {
        Transitions.emplace_back(Factory->getNode(Frt, std::move(NewPP)));
      }
    }
  } else {
    // We are filling out a partial pack
    std::vector<Instruction *> UsableInsts = PP->getUsableInsts(Frt);

    assert(!UsableInsts.empty());

    for (auto *I : UsableInsts) {
      std::unique_ptr<PartialPack> NextPP = PP->fillOneLane(I);
      if (!isPartialPackFeasible(*NextPP, Frt)) {
        continue;
      }
      if (auto *VP = NextPP->getPack()) {
        // Finished filling out this pack; move to the next frontier.
        float Cost;
        std::unique_ptr<Frontier> NextFrt = Frt->advance(VP, Cost, TTI);
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
  for (unsigned Iter = 0; Iter < NumIters; Iter++) {
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
    std::vector<const VectorPack *> Extensions = findExtensionPacks(FrtScratch);

    if (!Extensions.empty()) {
      auto *VP = Extensions[rand_int(Extensions.size())];
      Cost += FrtScratch.advanceInplace(VP, TTI);
    } else {
      for (auto *V : FrtScratch.usableInsts()) {
        auto *I = cast<Instruction>(V);
        Cost += FrtScratch.advanceInplace(I, TTI);
        break;
      }
    }
    if (FrtScratch.getUnresolvedPacks().empty() &&
        FrtScratch.numUnresolvedScalars() == 0)
      break;
  }
  return Cost;
}
