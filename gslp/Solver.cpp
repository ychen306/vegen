#include "Solver.h"
#include "MatchManager.h"
#include "VectorPackSet.h"
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
      if (UserInst) {
        if (UserInst->getParent() != BB)
          // Mark that `I` has a scalar use.
          UnresolvedScalars.set(InstId);
        else
          // `I` is used by some other instruction in `BB`
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

void Frontier::freezeOneInst(Instruction *I) {
  unsigned InstId = VPCtx->getScalarId(I);
  //assert(FreeInsts.test(InstId));
  if (!FreeInsts.test(InstId))
    return;
  FreeInsts.reset(InstId);
  UnresolvedScalars.reset(InstId);
  UsableInsts.reset(InstId);

  // See if freezing `I` makes any of its operands *usable*
  for (Value *Operand : I->operands()) {
    auto OI = dyn_cast<Instruction>(Operand);
    if (!OI || OI->getParent() != BB)
      continue;

    bool Usable = true;
    if (!isFree(OI))
      continue;

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
    if (!V)
      continue;
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
    assert(VecTy->getNumElements() == OP->size());

    // Special case: we can build OP by broadcasting `I`.
    if (is_splat(*OP) && (*OP)[0] == I) {
      Cost += TTI->getShuffleCost(TargetTransformInfo::SK_Broadcast, VecTy, 0);
      ResolvedPackIds.push_back(i);
      continue;
    }

    // FIXME: Consider the case of *partial* resuse here.
    // E.g. If we have two operand packs (a,b) and (b,a) then we can
    // just explicitly pack (a,b) with insertion and get (b,a) with permutation.
    for (unsigned i = 0; i < OP->size(); i++) {
      // Pay the insert cost
      if ((*OP)[i] == I)
        Cost +=
            2 * TTI->getVectorInstrCost(Instruction::InsertElement, VecTy, i);
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
    if (!V)
      continue;
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

  return 0.5;
  return 2;
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
    if (!OutputLanes[LaneId])
      continue;
    auto *I = dyn_cast<Instruction>(OutputLanes[LaneId]);
    if (!I)
      continue;
    unsigned InstId = VPCtx->getScalarId(I);

    // Pay the extract cost
    if (UnresolvedScalars.test(InstId))
      Cost +=
          TTI->getVectorInstrCost(Instruction::ExtractElement, VecTy, LaneId);
  }

  // FIXME: instead of doing this, which is broken if some intermediate values
  // have external user, directly subtract cost of dead instructions. We have
  // enough information to check if a value is dead.
  auto ReplacedInsts = VP->getReplacedInsts();
  std::sort(ReplacedInsts.begin(), ReplacedInsts.end(),
            [](Instruction *I, Instruction *J) { return J->comesBefore(I); });
  for (auto *I : ReplacedInsts)
    freezeOneInst(I);

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
      if (!V)
        continue;
      if (isa<Constant>(V))
        continue;
      auto *I = dyn_cast<Instruction>(V);
      if (!I || I->getParent() != BB) {
        // Assume I is always scalar and pay the insert cost.
        Cost += 2 * TTI->getVectorInstrCost(Instruction::InsertElement,
                                            OperandTy, LaneId);
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

float Frontier::advanceInplace(ShuffleTask ST, TargetTransformInfo *TTI) {
  auto It = std::lower_bound(UnresolvedPacks.begin(), UnresolvedPacks.end(),
                             ST.Output);
  assert(It != UnresolvedPacks.end());
  assert(*It == ST.Output);
  std::swap(*It, UnresolvedPacks.back());
  UnresolvedPacks.pop_back();
  for (auto *OP : ST.Inputs)
    UnresolvedPacks.push_back(OP);
  std::sort(UnresolvedPacks.begin(), UnresolvedPacks.end());
  return ST.getCost(TTI);
}

raw_ostream &operator<<(raw_ostream &OS, const OperandPack &OP) {
  OS << "[";
  for (auto *V : OP)
    if (V->getName().size() == 0)
      errs() << *V;
    else
      errs() << V->getName() << ", ";
  OS << "]";
  return OS;
}

raw_ostream &operator<<(raw_ostream &OS, const ShuffleTask &ST) {
  OS << *ST.Output << "\t\n->\n" << "{\n";
  for (auto *OP : ST.Inputs)
    OS << *OP << '\n';
  OS << "}\n";
  return OS;
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
  return Next;
}

std::unique_ptr<Frontier> Frontier::advance(ShuffleTask ST, float &Cost,
                                            TargetTransformInfo *TTI) const {
  auto Next = std::make_unique<Frontier>(*this);
  Cost = Next->advanceInplace(ST, TTI);
  return Next;
}

// If we already have a UCTNode for the same frontier, reuse that node.
UCTNode *UCTNodeFactory::getNode(std::unique_ptr<Frontier> Frt) {
  decltype(FrontierToNodeMap)::iterator It;
  bool Inserted;
  std::tie(It, Inserted) = FrontierToNodeMap.try_emplace(Frt.get(), nullptr);
  assert(Inserted);
  if (Inserted) {
    It->first = Frt.get();
    auto *NewNode = new UCTNode(Frt.get());
    Nodes.push_back(std::unique_ptr<UCTNode>(NewNode));
    It->second = NewNode;
    Frontiers.push_back(std::move(Frt));
  }
  return It->second;
}

// Assuming all elements of `OP` are loads, try to find an extending load pack.
static VectorPack *findExtendingLoadPack(const OperandPack &OP, BasicBlock *BB,
                                         Packer *Pkr) {
  // errs() << "Finding vector load to extend: {\n";
  // for (auto *V : OP)
  //  if (V)
  //    errs() << "\t" << *V << '\n';
  // errs() << "}\n\n";
  auto *VPCtx = Pkr->getContext(BB);
  auto &LoadDAG = Pkr->getLoadDAG(BB);
  auto &LDA = Pkr->getLDA(BB);

  // The set of loads producing elements of `OP`
  SmallPtrSet<Instruction *, 8> LoadSet;
  for (auto *V : OP) {
    if (!V)
      continue;
    if (auto *I = dyn_cast<Instruction>(V))
      LoadSet.insert(I);
  }

  // The loads might jumbled.
  // In other words, any one of the lanes could be the leading load
  for (auto *V : OP) {
    if (!V)
      continue;
    auto *LeadLI = cast<LoadInst>(V);
    BitVector Elements(VPCtx->getNumValues());
    BitVector Depended(VPCtx->getNumValues());
    Elements.set(VPCtx->getScalarId(LeadLI));
    Depended |= LDA.getDepended(LeadLI);
    std::vector<LoadInst *> Loads{LeadLI};

    LoadInst *CurLoad = LeadLI;
    while (Elements.count() < LoadSet.size()) {
      auto It = LoadDAG.find(CurLoad);
      // End of the chain
      if (It == LoadDAG.end())
        break;

      LoadInst *NextLI = nullptr;
      // Only use the next load in the load set
      for (auto *Next : It->second) {
        if (LoadSet.count(Next)) {
          NextLI = cast<LoadInst>(Next);
          break;
        }
      }
      if (!NextLI) {
        // load a don't care to fill the gap
        Loads.push_back(nullptr);
        CurLoad = cast<LoadInst>(*It->second.begin());
        continue;
      }
      if (!checkIndependence(LDA, *VPCtx, NextLI, Elements, Depended))
        break;
      Loads.push_back(NextLI);
      Elements.set(VPCtx->getScalarId(NextLI));
      Depended |= LDA.getDepended(NextLI);
      CurLoad = NextLI;
    }
    if (Elements.count() == LoadSet.size()) {
      // Pad
      while (Loads.size() < PowerOf2Ceil(OP.size()))
        Loads.push_back(nullptr);
      return VPCtx->createLoadPack(Loads, Elements, Depended, Pkr->getTTI());
    }
  }
  // errs() << "Failed!\n";
  return nullptr;
}

class SlotSet {
  std::vector<LoadInst *> Slots;
  unsigned MinId, MaxId;
  unsigned NumElems = 0;
  unsigned HasValue = false;

public:
  LoadInst *operator[](unsigned i) const { return Slots[i]; }
  bool try_insert(unsigned i, LoadInst *LI) {
    if (i >= Slots.size())
      Slots.resize(i + 1);
    if (!Slots[i] || Slots[i] == LI) {
      Slots[i] = LI;
      if (HasValue) {
        MinId = std::min(i, MinId);
        MaxId = std::max(i, MaxId);
      } else {
        MinId = MaxId = i;
        HasValue = true;
      }
      NumElems++;
      return true;
    }
    return false;
  }

  double utilization() const { return (double)NumElems / (MaxId - MinId + 1); }

  unsigned num_elems() const { return NumElems; }

  unsigned minId() const { return MinId; }

  unsigned maxId() const { return MaxId; }
};


// Try to coalesce main pack with some other packs
static VectorPack *tryCoalesceLoads(const VectorPack *MainPack,
                                    ArrayRef<VectorPack *> OtherPacks,
                                    Packer *Pkr) {
  auto *BB = MainPack->getBasicBlock();
  auto &LayoutInfo = Pkr->getLoadInfo(BB);
  // Full, can't coalesce
  if (MainPack->getOrderedValues().size() == MainPack->getElements().count())
    return nullptr;

  auto *SomeLoad = *MainPack->elementValues().begin();
  auto *Leader = LayoutInfo.get(cast<Instruction>(SomeLoad)).Leader;
  BitVector Elements = MainPack->getElements();
  BitVector Depended = MainPack->getDepended();
  SlotSet Slots;
  for (auto *V : MainPack->elementValues()) {
    auto *LI = cast<LoadInst>(V);
    unsigned SlotId = LayoutInfo.get(LI).Id;
    Slots.try_insert(SlotId, LI);
  }

  for (auto *Other : OtherPacks) {
    auto &Info =
        LayoutInfo.get(cast<Instruction>(Other->getOrderedValues()[0]));
    // Cannot coalesce with loads accessing a different object
    if (Info.Leader != Leader)
      continue;
    // Cannot coalesce if not independent
    if (Depended.anyCommon(Other->getElements()) ||
        Other->getDepended().anyCommon(Elements))
      continue;

    auto Temp = Slots;
    bool Coalesced = true;
    for (auto *V : Other->elementValues()) {
      auto *LI = cast<LoadInst>(V);
      unsigned SlotId = LayoutInfo.get(LI).Id;
      // Can only coalesce if the slot if empty
      bool Ok = Temp.try_insert(SlotId, LI);
      ;
      if (!Ok) {
        Coalesced = false;
        break;
      }
    }
    if (Coalesced && Temp.utilization() > Slots.utilization()) {
      Slots = Temp;
      Depended |= Other->getDepended();
      Elements |= Other->getElements();
    }
  }

  if (Elements == MainPack->getElements())
    return nullptr;

  std::vector<LoadInst *> Loads;
  for (unsigned i = Slots.minId(), e = Slots.maxId(); i != e; i++) {
    Loads.push_back(Slots[i]);
  }

  return Pkr->getContext(BB)->createLoadPack(Loads, Elements, Depended,
                                             Pkr->getTTI());
}

// Remove duplicate elements in OP
static const OperandPack *dedup(VectorPackContext *VPCtx, const OperandPack *OP) {
  return OP;
  SmallPtrSet<Value *, 4> Seen;
  OperandPack Deduped;
  for (auto *V : *OP) {
    bool Inserted = Seen.insert(V).second;
    if (!Inserted)
      continue;
    Deduped.push_back(V);
  }
  // Fast path for when we've removed nothing
  if (Deduped.size() == OP->size())
    return OP;
  return VPCtx->getCanonicalOperandPack(Deduped);
}


static std::vector<VectorPack *> findExtensionPacks(const Frontier &Frt) {
  auto *Pkr = Frt.getPacker();
  auto *BB = Frt.getBasicBlock();
  auto &LDA = Pkr->getLDA(BB);
  auto *VPCtx = Pkr->getContext(BB);
  auto *TTI = Pkr->getTTI();
  auto &LoadDAG = Pkr->getLoadDAG(BB);
  auto &MM = Pkr->getMatchManager(BB);

  // Put load extensions in a separate category.
  // We don't extend with a load pack if we can extend with other arithmetic
  // packs
  std::vector<VectorPack *> LoadExtensions;

  std::vector<VectorPack *> Extensions;
  for (auto *OP : Frt.getUnresolvedPacks()) {
    OP = dedup(VPCtx, OP);
    ////////
    //errs() << "Looking for a pack to extend:{\n";
    //for (auto *V : *OP)
    //  if (V)
    //    errs() << *V << '\n';
    //  else
    //    errs() << "undef\n";
    //errs() << "}\n";
    ///////

    //if (!Extensions.empty())
    //  break;

    unsigned NumLanes = OP->size();
    BitVector Elements(VPCtx->getNumValues());
    BitVector Depended(VPCtx->getNumValues());
    bool Extensible = true;
    bool AllLoads = true;
    bool HasUndef = false;
    for (unsigned i = 0; i < NumLanes; i++) {
      auto *V = (*OP)[i];
      if (!V) {
        HasUndef = true;
        continue;
      }
      auto *I = dyn_cast<Instruction>(V);
      if (!I) {
        AllLoads = false;
        continue;
      }

      if (!isa<LoadInst>(I))
        AllLoads = false;

      if (!I || I->getParent() != BB || !Frt.isUsable(I)) {
        //errs() << "BAD INST: " << *I << ", usable? " << Frt.isUsable(I) << '\n';
        Extensible = false;
        break;
      }
      unsigned InstId = VPCtx->getScalarId(I);
      if (!checkIndependence(LDA, *VPCtx, I, Elements, Depended)) {
        //errs() << "BREAKS DEPENDENCY: " << *I << '\n';
        Extensible = false;
        break;
      }
      Elements.set(InstId);
      Depended |= LDA.getDepended(I);
    }

    //errs() << "Extensible? " << Extensible << ", AllLoads? " << AllLoads
    //       << '\n';

    if (!Extensible)
      continue;

    if (AllLoads) {
      if (auto *LoadVP = findExtendingLoadPack(*OP, BB, Pkr))
        LoadExtensions.push_back(LoadVP);
      continue;
    }

    if (HasUndef)
      continue;

    for (auto *Inst : Pkr->getInsts()) {
      ArrayRef<BoundOperation> LaneOps = Inst->getLaneOps();
      if (LaneOps.size() != NumLanes)
        continue;

      std::vector<const Operation::Match *> Lanes;
      for (unsigned i = 0; i < NumLanes; i++) {
        ArrayRef<Operation::Match> Matches =
            MM.getMatchesForOutput(LaneOps[i].getOperation(), (*OP)[i]);
        if (Matches.empty())
          break;
        // FIXME: consider multiple matches for the same operation
        Lanes.push_back(&Matches[0]);
      }

      if (Lanes.size() == NumLanes) {
        Extensions.push_back(
            VPCtx->createVectorPack(Lanes, Elements, Depended, Inst, TTI));
      }
    }
  }

  if (!Extensions.empty())
    return Extensions;

  if (!LoadExtensions.empty()) {
    auto *LoadVP = LoadExtensions[0];
    if (auto *Coalesced = tryCoalesceLoads(
            LoadVP, ArrayRef<VectorPack *>(LoadExtensions).slice(1), Pkr)) {
      return {Coalesced, LoadVP};
    }
    return {LoadVP};
  }

  return {};
}

// Fill out the children node
void UCTNode::expand(unsigned MaxNumLanes, UCTNodeFactory *Factory,
    llvm::TargetTransformInfo *TTI) {
  assert(Transitions.empty() && "expanded already");
  auto *Pkr = getPacker();

  // We are not working w/ any partial pack, start partial packs!
  auto *BB = Frt->getBasicBlock();
  for (auto *V : Frt->usableInsts()) {
    auto *I = dyn_cast<Instruction>(V);
    if (!I)
      continue;
    float Cost;
    auto *Next = Factory->getNode(Frt->advance(I, Cost, TTI));
    Transitions.emplace_back(I, Next, Cost);
  }

  //// Also consider the extension packs
  for (auto *VP : findExtensionPacks(*Frt)) {
    float Cost;
    auto *Next = Factory->getNode(Frt->advance(VP, Cost, TTI));
    Transitions.emplace_back(VP, Next, Cost);
  }
}

// Do one iteration of MCTS
void UCTSearch::run(UCTNode *Root, unsigned NumIters) {
  struct FullTransition {
    UCTNode *Parent;
    UCTNode::Transition *T;
  };

  if (Root->expanded() && Root->transitions().size() == 1)
    NumIters = 1;

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

static float estimateAllScalarCost(const Frontier &Frt,
                                   TargetTransformInfo *TTI) {
  // errs() << "Finding vector load to extend: {\n";
  // for (auto *V : OP)
  //  if (V)
  //    errs() << "\t" << *V << '\n';
  // errs() << "}\n\n";
  auto *BB = Frt.getBasicBlock();
  float Cost = 0;
  // Pay insertion cost
  for (auto *OP : Frt.getUnresolvedPacks()) {
    auto *VecTy = getVectorType(*OP);
    for (unsigned i = 0, e = OP->size(); i != e; i++) {
      auto *V = (*OP)[i];
      if (!V)
        continue;
      auto *I = dyn_cast<Instruction>(V);
      if (!I || I->getParent() != BB || !Frt.isFree(I))
        continue;
      if (i == 0 && is_splat(*OP)) {
        Cost +=
            TTI->getShuffleCost(TargetTransformInfo::SK_Broadcast, VecTy, 0);
        break;
      }
      Cost += 2 * TTI->getVectorInstrCost(Instruction::InsertElement, VecTy, i);
    }
  }
  return Cost;
}


std::vector<VectorPack *> RolloutEvaluator::getExtensions(const Frontier &Frt) {
  return findExtensionPacks(Frt);
  auto It = ExtensionCache.find(&Frt);
  if (It != ExtensionCache.end())
    return It->second;
  Frontiers.push_back(std::make_unique<Frontier>(Frt));
  return ExtensionCache[Frontiers.back().get()] = findExtensionPacks(Frt);
}

// Uniformly random rollout
float RolloutEvaluator::evaluate(const Frontier *Frt) {
  auto *Pkr = Frt->getPacker();
  auto *TTI = Pkr->getTTI();
  auto ScratchFrt = *Frt;
  std::vector<VectorPack *> Extensions = getExtensions(ScratchFrt);
  float Cost = 0;
  while (!Extensions.empty()) {
    auto *VP = Extensions[rand_int(Extensions.size())];
    Cost += ScratchFrt.advanceInplace(VP, TTI);
    Extensions = getExtensions(ScratchFrt);
  }
  return Cost + estimateAllScalarCost(ScratchFrt, TTI);
}

static VectorPack *findExtensionPack(const Frontier &Frt) {
  {
    auto Extensions = findExtensionPacks(Frt);

    if (Extensions.empty())
      return nullptr;

    // Take the extension pack with the lowest local cost
    std::sort(Extensions.begin(), Extensions.end(),
        [](const VectorPack *A, const VectorPack *B) {
        return A->getCost() < B->getCost();
        });
    return Extensions[0];
  }
  auto *Pkr = Frt.getPacker();
  auto *BB = Frt.getBasicBlock();
  auto &LDA = Pkr->getLDA(BB);
  auto *VPCtx = Pkr->getContext(BB);
  auto *TTI = Pkr->getTTI();
  auto &LoadDAG = Pkr->getLoadDAG(BB);
  auto &MM = Pkr->getMatchManager(BB);

  std::vector<VectorPack *> Extensions;
  for (auto *OP : Frt.getUnresolvedPacks()) {
    // errs() << "Looking for a pack to extend:{\n";
    // for (auto *V : *OP)
    //  if (V) errs() << *V << '\n';
    // errs() << "}\n";

    unsigned NumLanes = OP->size();
    BitVector Elements(VPCtx->getNumValues());
    BitVector Depended(VPCtx->getNumValues());
    bool Extensible = true;
    bool AllLoads = true;
    for (unsigned i = 0; i < NumLanes; i++) {
      auto *V = (*OP)[i];
      // TODO: support nop lane
      if (!V) {
        Extensible = false;
        break;
      }
      auto *I = dyn_cast<Instruction>(V);
      if (!I) {
        AllLoads = false;
        continue;
      }
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

    // errs() << "Extensible? " << Extensible
    //  << ", AllLoads? " << AllLoads << '\n';

    if (!Extensible)
      continue;

    if (AllLoads) {
      if (auto *LoadVP = findExtendingLoadPack(*OP, BB, Pkr))
        Extensions.push_back(LoadVP);
      continue;
    }
    for (auto *Inst : Pkr->getInsts()) {
      ArrayRef<BoundOperation> LaneOps = Inst->getLaneOps();
      if (LaneOps.size() != NumLanes)
        continue;

      std::vector<const Operation::Match *> Lanes;
      for (unsigned i = 0; i < NumLanes; i++) {
        ArrayRef<Operation::Match> Matches =
            MM.getMatchesForOutput(LaneOps[i].getOperation(), (*OP)[i]);
        if (Matches.empty())
          break;
        // FIXME: consider multiple matches for the same operation
        Lanes.push_back(&Matches[0]);
      }

      if (Lanes.size() == NumLanes) {
        Extensions.push_back(
            VPCtx->createVectorPack(Lanes, Elements, Depended, Inst, TTI));
      }
    }
  }

  if (Extensions.empty())
    return nullptr;

  for (auto *VP : Extensions)
    if (VP->getProducer() && VP->getProducer()->getName().contains("_madd_"))
      return VP;

  // Take the extension pack with the lowest local cost
  std::sort(Extensions.begin(), Extensions.end(),
            [](const VectorPack *A, const VectorPack *B) {
              return A->getCost() < B->getCost();
            });
  return Extensions[0];
}

float estimateCost(Frontier Frt, VectorPack *VP) {
  auto *Pkr = Frt.getPacker();
  auto *BB = Frt.getBasicBlock();
  auto &LDA = Pkr->getLDA(BB);
  auto *VPCtx = Pkr->getContext(BB);
  auto *TTI = Pkr->getTTI();

  float Cost = Frt.advanceInplace(VP, TTI);
  for (;;) {
    auto *ExtVP = findExtensionPack(Frt);
    if (!ExtVP)
      break;
    Cost += Frt.advanceInplace(ExtVP, TTI);
    // errs() << "!!! Extending with: "<< *ExtVP << ", COST AFTER EXTENSION = "
    // << Cost << '\n';
  }

  while (Frt.numUnresolvedScalars() != 0 || Frt.getUnresolvedPacks().size()) {
    for (auto *V : Frt.usableInsts()) {
      if (auto *I = dyn_cast<Instruction>(V)) {
        Cost += Frt.advanceInplace(I, TTI);
        // errs() << "!!! Scalarizing "<< *I << ", COST AFTER = " << Cost <<
        // '\n';
        break;
      }
    }
  }

  // errs() << "!!! est cost : " << Cost << " of  " << *VP << '\n';
  return Cost;
}

// Hack! purely for debugging
struct : public BackwardShuffle {
  std::vector<const OperandPack *>
  run(const VectorPackContext *VPCtx,
      const OperandPack *Output) const override {
    if (Output->size() != 16)
      return {};
    std::map<unsigned, OperandPack> ShuffleOperands;
    for (auto *V : *Output) {
      auto *I = dyn_cast<Instruction>(V);
      if (!I)
        return {};
      ShuffleOperands[I->getOpcode()].push_back(V);
    }
    if (ShuffleOperands.size() != 2)
      return {};
    auto *OP1 = VPCtx->getCanonicalOperandPack(ShuffleOperands.begin()->second);
    auto *OP2 = VPCtx->getCanonicalOperandPack(std::next(ShuffleOperands.begin())->second);
    if (OP1 == OP2)
      return {OP1};
    return {OP1, OP2};
  }
  float getCost(llvm::TargetTransformInfo *) const override { return 1.0; }
} DeInterleave;

class DPSolver {
  struct Solution {
    float Cost;
    const VectorPack *VP;
    Optional<ShuffleTask> ST;

    // Default solution is no extension
    Solution() = default;
    Solution(float Cost, VectorPack *VP) : Cost(Cost), VP(VP) {}
    Solution(float Cost, ShuffleTask TheST) : Cost(Cost), VP(nullptr), ST(ST) {}
  };
  TargetTransformInfo *TTI;

  DenseMap<const Frontier *, Solution, FrontierHashInfo> Solutions;
  std::vector<std::unique_ptr<Frontier>> Frontiers;

  Solution solveImpl(const Frontier &Frt) {
    // Figure out the cost of not adding any extensions.
    Solution Sol;
    Sol.VP = nullptr;
    Sol.Cost = 0;
    Sol.Cost = estimateAllScalarCost(Frt, TTI);

    //errs() << "============== FRONTIER STATE ==========\n";
    //errs() << "UNRESOLVED VECTOR OPERANDS: <<<<<<<<<<<<<<<<<<<<<<\n";
    //for (auto *OP : Frt.getUnresolvedPacks())
    //  errs() << *OP << '\n';
    //errs() << ">>>>>>>>>>>>>>>\n";
    //errs() << "UNRESOLVED SCALAR OPERANDS: <<<<<<<<<<<<\n";
    //for (auto *V : Frt.getUnresolvedScalars())
    //  errs() << V->getName() << ", ";
    //errs() << ">>>>>>>>>>>>>>>\n";

    // Figure out the cost of adding one extension
    auto Extensions = findExtensionPacks(Frt);
    // errs() << "NUM EXTENSIONS: " << Extensions.size() << '\n';
    for (const VectorPack *ExtVP : Extensions) {
      float LocalCost;
      auto NextFrt = Frt.advance(ExtVP, LocalCost, TTI);

      float TotalCost = solve(std::move(NextFrt)).Cost + LocalCost;
      //errs() << " EXTENDING WITH " << *ExtVP
      //       << ", transition cost : " << LocalCost
      //       << ", local cost : " << ExtVP->getCost()
      //       << ", total cost : " << TotalCost
      //       << ", num elems: " << ExtVP->getOrderedValues().size()
      //       << ", best cost so far: " << Sol.Cost << '\n';

      if (Sol.Cost > TotalCost) {
        Sol.Cost = TotalCost;
        Sol.VP = ExtVP;
      }
    }

#if 0
    auto *VPCtx = Frt.getContext();
    for (auto *OP : Frt.getUnresolvedPacks()) {
      ShuffleTask ST(&DeInterleave, OP, VPCtx);
      if (!ST.feasible())
        continue;

      float LocalCost;
      auto NextFrt = Frt.advance(ST, LocalCost, TTI);

      float TotalCost = solve(std::move(NextFrt)).Cost + LocalCost;
      errs() << " EXTENDING WITH Shuffle " << ST
             << ", transition cost : " << LocalCost
             << ", total cost : " << TotalCost
             << ", best cost so far: " << Sol.Cost << '\n';
      if (Sol.Cost > TotalCost) {
        Sol.Cost = TotalCost;
        Sol.VP = nullptr;
        Sol.ST = ST;
      }
    }
#endif

    // Also try shuffle
    return Sol;
  }

public:
  DPSolver(TargetTransformInfo *TTI) : TTI(TTI), Solutions(1000000) {}

  Solution solve(const Frontier &Frt) {
    auto It = Solutions.find(&Frt);
    // Solved already
    if (It != Solutions.end())
      return It->second;

    auto Sol = solveImpl(Frt);
    Frontiers.push_back(std::make_unique<Frontier>(Frt));
    return Solutions[Frontiers.back().get()] = Sol;
  }

  Solution solve(std::unique_ptr<Frontier> Frt) {
    auto It = Solutions.find(Frt.get());
    // Solved already
    if (It != Solutions.end())
      return It->second;

    auto Sol = solveImpl(*Frt);
    Frontiers.push_back(std::move(Frt));
    return Solutions[Frontiers.back().get()] = Sol;
  }
};

std::vector<VectorPack *> getSeedStorePacks(const Frontier &Frt, StoreInst *SI,
                                            unsigned VL) {
  if (!Frt.isUsable(SI)) {
    return {};
  }

  auto *Pkr = Frt.getPacker();
  auto *BB = Frt.getBasicBlock();
  auto &LDA = Pkr->getLDA(BB);
  auto *VPCtx = Pkr->getContext(BB);
  auto *TTI = Pkr->getTTI();
  auto &StoreDAG = Pkr->getStoreDAG(BB);

  std::vector<VectorPack *> Seeds;

  std::function<void(std::vector<StoreInst *>, BitVector, BitVector)>
      Enumerate = [&](std::vector<StoreInst *> Stores, BitVector Elements,
                      BitVector Depended) {
        if (Stores.size() == VL) {
          Seeds.push_back(
              VPCtx->createStorePack(Stores, Elements, Depended, TTI));
          return;
        }

        auto It = StoreDAG.find(Stores.back());
        if (It == StoreDAG.end()) {
          return;
        }
        for (auto *Next : It->second) {
          auto *NextSI = cast<StoreInst>(Next);
          if (!Frt.isUsable(NextSI)) {
            continue;
          }
          if (!checkIndependence(LDA, *VPCtx, NextSI, Elements, Depended)) {
            continue;
          }
          auto StoresExt = Stores;
          auto ElementsExt = Elements;
          auto DependedExt = Depended;
          StoresExt.push_back(NextSI);
          ElementsExt.set(VPCtx->getScalarId(NextSI));
          DependedExt |= LDA.getDepended(NextSI);
          Enumerate(StoresExt, ElementsExt, DependedExt);
        }
      };

  std::vector<StoreInst *> Stores{SI};
  BitVector Elements(VPCtx->getNumValues());
  BitVector Depended(VPCtx->getNumValues());

  Elements.set(VPCtx->getScalarId(SI));
  Depended |= LDA.getDepended(SI);

  Enumerate(Stores, Elements, Depended);
  return Seeds;
}

VectorPack *getSeedStorePack(const Frontier &Frt, StoreInst *SI, unsigned VL) {
  auto Seeds = getSeedStorePacks(Frt, SI, VL);
  if (Seeds.empty())
    return nullptr;
  return Seeds[0];
}

float optimizeBottomUp(VectorPackSet &Packs, Packer *Pkr, BasicBlock *BB) {
  Frontier Frt(BB, Pkr);
  auto &StoreDAG = Pkr->getStoreDAG(BB);

  DenseMap<Instruction *, unsigned> StoreChainLen;
  std::function<unsigned(Instruction *)> GetChainLen =
      [&](Instruction *I) -> unsigned {
    if (StoreChainLen.count(I))
      return StoreChainLen[I];
    auto It = StoreDAG.find(I);
    if (It == StoreDAG.end())
      return StoreChainLen[I] = 1;
    unsigned MaxLen = 0;
    for (auto *Next : It->second) {
      MaxLen = std::max<unsigned>(MaxLen, GetChainLen(Next));
    }
    return StoreChainLen[I] = MaxLen + 1;
  };

  std::vector<StoreInst *> Stores;
  for (auto &StoreAndNext : StoreDAG)
    Stores.push_back(cast<StoreInst>(StoreAndNext.first));

  // Sort stores by store chain length
  std::sort(Stores.begin(), Stores.end(), [&](StoreInst *A, StoreInst *B) {
    return GetChainLen(A) > GetChainLen(B);
  });

  errs() << "??? num stores: " << Stores.size() << '\n';

  auto *TTI = Pkr->getTTI();

  DPSolver Solver(TTI);

  std::vector<unsigned> VL{64, 32, 16, 8, 4, 2};
  //std::vector<unsigned> VL{16, 8, 4, 2};
  //std::vector<unsigned> VL { 8 };
  float Cost = 0;
  float BestEst = 0;

  for (unsigned i : VL) {
    for (auto *SI : Stores) {
      auto *SeedVP = getSeedStorePack(Frt, SI, i);
      if (SeedVP) {
        if (SeedVP) {
           Cost += Frt.advanceInplace(SeedVP, TTI);
           Packs.tryAdd(SeedVP);
           continue;
        }
#if 1
        float Est = estimateCost(Frt, SeedVP);
#else
        float LocalCost;
        auto Sol = Solver.solve(Frt.advance(SeedVP, LocalCost, TTI));
        float Est = LocalCost + Sol.Cost;
#endif
        //errs() << "Estimated cost of " << *SeedVP << " is " << Est
        //       << ", local cost: " << LocalCost << ", trans cost: " << Sol.Cost
        //       << '\n';
        if (Est < BestEst) {
#if 1
           Cost += Frt.advanceInplace(SeedVP, TTI);
           Packs.tryAdd(SeedVP);
           BestEst = Est;

#else
          //////////////
          Cost += Frt.advanceInplace(SeedVP, TTI);
          Packs.tryAdd(SeedVP);
          for (;;) {
            // errs() << "!!! Adding : " << *ExtVP << '\n';
            // errs() << "\t updated cost: " << Cost << '\n';
            auto Sol = Solver.solve(Frt);
            if (auto *ExtVP = Sol.VP) {
              Cost += Frt.advanceInplace(ExtVP, TTI);
              Packs.tryAdd(ExtVP);
            } else if (Sol.ST) {
              Cost += Frt.advanceInplace(Sol.ST.getValue(), TTI);
            } else {
              break;
            }
          }
          BestEst = estimateAllScalarCost(Frt, TTI);
          /////////////
#endif
        }
      }
    }
  }
  UCTNodeFactory Factory;
  RolloutEvaluator Evaluator;
  UCTSearch MCTS(0.1/*c*/, 0/*w*/, 0/*ExpandThreshold*/, &Factory, Pkr,
                 nullptr/*Policy*/, &Evaluator, TTI);
  UCTNode *Root = Factory.getNode(std::make_unique<Frontier>(Frt));
  unsigned NumSimulations = 1000;
  float TotalCost = 0;
  while (!Root->isTerminal()) {
    MCTS.run(Root, NumSimulations);
    assert(Root->expanded());

    auto &Transitions = Root->transitions();

    UCTNode::Transition *T;
    if (Transitions.size() == 1) {
      T = &*Transitions.begin();
    } {
      T = &*std::max_element(Transitions.begin(), Transitions.end(),

          [](const UCTNode::Transition &A, const UCTNode::Transition &B) {
              float ACost = -A.Cost - A.Next->minCost();
              float BCost = -B.Cost - B.Next->minCost();
            return std::tie(ACost, A.Count) < std::tie(BCost, B.Count);
          }
                              );
    }


    auto Node = Root;
    errs() << "====================================="
           << "\n\t t transition cost: " << T->transitionCost()
           << "\n\t num transitions: " << Transitions.size()
           << "\n\t scalar cost: " << Transitions.begin()->avgCost()
           << "\n\t t avg cost: " << T->avgCost()
           << "\n\t t->next avg cost: " << T->Next->avgCost()
           << "\n\t t->next min cost: " << T->Next->minCost()
           << "\n\t t->next terminal? " << T->Next->isTerminal()
           << "\n\t t visit count : " << T->visitCount()
           << "\n\t node visit count: " << Node->visitCount()
           << "\n\t min cost : " << Node->minCost()
           << "\n\t max cost : " << Node->maxCost()
           << "\n\t avg cost : " << Node->avgCost()
           << "\n\t num unresolved packs : "
           << Node->getFrontier()->getUnresolvedPacks().size()
           << "\n\t num unresolved scalars : "
           << Node->getFrontier()->numUnresolvedScalars() << '\n';

    if (T->VP) {
      errs() << "[MCTS] ADDING: " << *T->VP << '\n';
      Packs.tryAdd(T->VP);
    }
    Root = T->Next;
    TotalCost += T->transitionCost();
      errs() << "[MCTS} New cost: " << TotalCost << '\n';

  }
#if 0
  for (;;) {
#if 0
    auto *ExtVP = findExtensionPack(Frt);
#else
    auto *ExtVP = Solver.solve(Frt).VP;
#endif

    if (!ExtVP)
      break;
    Cost += Frt.advanceInplace(ExtVP, TTI);
    // errs() << "!!! Adding : " << *ExtVP << '\n';
    // errs() << "\t updated cost: " << Cost << '\n';
    Packs.tryAdd(ExtVP);
  }

  while (Frt.numUnresolvedScalars() != 0 || Frt.getUnresolvedPacks().size()) {
    for (auto *V : Frt.usableInsts()) {
      if (auto *I = dyn_cast<Instruction>(V)) {
        // errs() << "!!! scalarizing: " << *I << '\n';
        Cost += Frt.advanceInplace(I, TTI);
        // errs() << "\t updated cost: " << Cost << '\n';
        break;
      }
    }
  }
#endif

  return Cost;
}
