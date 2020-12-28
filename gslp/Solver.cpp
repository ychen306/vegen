#include "Solver.h"
#include "Heuristic.h"
#include "MatchManager.h"
#include "VectorPackSet.h"
#include "Embedding.h"
#include "llvm/Support/CommandLine.h"
#include <queue>

using namespace llvm;

extern cl::opt<bool> AggressivePacking;

static cl::opt<unsigned> MaxSearchDist(
    "max-search-dist",
    cl::value_desc(
        "Max distance with which we consider two instructions packable."),
    cl::init(20));

static cl::opt<bool> UseMCTS("use-mcts",
                             cl::desc("Use tree search during optimization"),
                             cl::init(false));

static unsigned computeHash(const Frontier *Frt) {
  unsigned Hash = 0;
  for (auto *OP : Frt->getUnresolvedPacks())
    Hash ^= OP->Hash;
  auto *VPCtx = Frt->getContext();
  for (auto *V : Frt->getUnresolvedScalars())
    Hash ^= VPCtx->getHashValue2(V);
  for (unsigned i : Frt->getFreeInsts().set_bits())
    Hash ^= VPCtx->getHashValue(i);
  return Hash;
}

Frontier::Frontier(BasicBlock *BB, Packer *Pkr)
    : Pkr(Pkr), BB(BB), VPCtx(Pkr->getContext(BB)),
      UnresolvedScalars(VPCtx->getNumValues(), false),
      FreeInsts(VPCtx->getNumValues(), true),
      UsableInsts(VPCtx->getNumValues(), false) {
  Hash = 0;
  // Find external uses of any instruction `I` in `BB`
  // and mark `I` as an unresolved scalar.
  for (auto &I : *BB) {
    bool AllUsersResolved = true;
    unsigned InstId = VPCtx->getScalarId(&I);
    Hash ^= VPCtx->getHashValue(InstId);
    for (User *U : I.users()) {
      auto UserInst = dyn_cast<Instruction>(U);
      if (UserInst) {
        if (UserInst->getParent() != BB) {
          // Mark that `I` has a scalar use.
          if (UnresolvedScalars.test(InstId)) {
            UnresolvedScalars.set(InstId);
            Hash ^= VPCtx->getHashValue2(InstId);
          }
        } else
          // `I` is used by some other instruction in `BB`
          AllUsersResolved = false;
      }
    }

    if (AllUsersResolved || isa<PHINode>(&I))
      UsableInsts.set(InstId);
  }
  assert(Hash == computeHash(this));
}

void Frontier::freezeOneInst(Instruction *I) {
  unsigned InstId = VPCtx->getScalarId(I);
  // assert(FreeInsts.test(InstId));
  if (!FreeInsts.test(InstId))
    return;
  Hash ^= VPCtx->getHashValue(InstId);
  if (UnresolvedScalars.test(InstId))
    Hash ^= VPCtx->getHashValue2(InstId);
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

bool Frontier::resolved(const OperandPack &OP) const {
  return !Pkr->getProducerInfo(VPCtx, &OP).Elements.anyCommon(FreeInsts);
}

float Frontier::advanceInplace(Instruction *I, TargetTransformInfo *TTI) {
  //float Cost = 0;
  float Cost = Pkr->getScalarCost(I);
  freezeOneInst(I);

  // Go over unresolved packs and see if we've resolved any lanes
  SmallVector<unsigned, 2> ResolvedPackIds;
  for (unsigned i = 0; i < UnresolvedPacks.size(); i++) {
    auto *OP = UnresolvedPacks[i];
    auto *VecTy = getVectorType(*OP);
    assert(VecTy->getNumElements() == OP->size());

    // Special case: we can build OP by broadcasting `I`.
    if ((*OP)[0] == I && is_splat(*OP)) {
      Cost += TTI->getShuffleCost(TargetTransformInfo::SK_Broadcast, VecTy, 0);
      Hash ^= OP->Hash;
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
    if (resolved(*OP)) {
      Hash ^= OP->Hash;
      ResolvedPackIds.push_back(i);
    }
  }

  // If `I` uses any free instructions,
  // add those to the set of unresolved scalars.
  for (Value *Operand : I->operands()) {
    auto *I2 = dyn_cast<Instruction>(Operand);
    if (!I2 || I2->getParent() != BB)
      continue;
    unsigned InstId = VPCtx->getScalarId(I2);
    if (FreeInsts.test(InstId) && !UnresolvedScalars.test(InstId)) {
      UnresolvedScalars.set(InstId);
      Hash ^= VPCtx->getHashValue2(InstId);
    }
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

static float getGatherCost(VectorType *VecTy, ArrayRef<Value *> Vals,
                           const OperandPack &OpndPack,
                           TargetTransformInfo *TTI) {
  if (isConstantPack(OpndPack))
    return 0;

  if (Vals.size() == OpndPack.size()) {
    bool Exact = true;
    for (unsigned i = 0; i < Vals.size(); i++)
      Exact &= (Vals[i] == OpndPack[i]);

    // Best case:
    // If `VP` produces `OpndPack` exactly then we don't pay any thing
    if (Exact)
      return 0;

    // Second best case:
    // `VP` produces a permutation of `OpndPack`
    if (std::is_permutation(Vals.begin(), Vals.end(), OpndPack.begin()))
      return TTI->getShuffleCost(TargetTransformInfo::SK_PermuteSingleSrc,
                                 VecTy);
  }

  return 0.5;
}

// Return the cost of gathering from `VP` to `OpndPack`
static unsigned getGatherCost(const VectorPack &VP, const OperandPack &OpndPack,
                              TargetTransformInfo *TTI) {
  return getGatherCost(getVectorType(VP), VP.getOrderedValues(), OpndPack, TTI);
}

static unsigned getGatherCost(const OperandPack &OP,
                              const OperandPack &OpndPack,
                              TargetTransformInfo *TTI) {
  return getGatherCost(getVectorType(OP), OP, OpndPack, TTI);
}

// FIXME: this doesn't work when there are lanes in VP that cover multiple
// instructions.
float Frontier::advanceInplace(const VectorPack *VP, TargetTransformInfo *TTI) {
  //float Cost = VP->getCost();
  float Cost = VP->getProducingCost();

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
  for (auto *I : VP->getReplacedInsts())
    freezeOneInst(I);

  SmallVector<unsigned, 2> ResolvedPackIds;
  if (!VP->isStore()) {
    for (unsigned i = 0; i < UnresolvedPacks.size(); i++) {
      auto *OP = UnresolvedPacks[i];
      auto &OPI = Pkr->getProducerInfo(VPCtx, OP);

      if (OPI.Elements.anyCommon(VP->getElements())) {
        Cost += getGatherCost(*VP, *OP, TTI);
        if (resolved(*OP)) {
          Hash ^= OP->Hash;
          ResolvedPackIds.push_back(i);
        }
      }
    }
  }

  // Track the unresolved operand packs used by `VP`
  SmallPtrSet<const OperandPack *, 8> UnresolvedSet(UnresolvedPacks.begin(),
                                                    UnresolvedPacks.end());
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
    if (!resolved(*OpndPack)) {
      bool Inserted = UnresolvedSet.insert(OpndPack).second;
      if (Inserted) {
        Hash ^= OpndPack->Hash;
        UnresolvedPacks.push_back(OpndPack);
      }
    }
  }

  remove(UnresolvedPacks, ResolvedPackIds);
  std::sort(UnresolvedPacks.begin(), UnresolvedPacks.end());
  return Cost;
}

raw_ostream &operator<<(raw_ostream &OS, const OperandPack &OP) {
  OS << "[";
  for (auto *V : OP)
    if (V) {
      if (V->getName().size() == 0)
        errs() << *V << ", ";
      else
        errs() << V->getName() << ", ";
    } else
      errs() << "undef\n";
  OS << "]";
  return OS;
}

static std::vector<const VectorPack *>
findExtensionPacks(const Frontier &Frt,
                   const CandidatePackSet *CandidateSet = nullptr);

raw_ostream &operator<<(raw_ostream &OS, const Frontier &Frt) {
  OS << "============== FRONTIER STATE ==========\n";
  OS << "UNRESOLVED VECTOR OPERANDS: <<<<<<<<<<<<<<<<<<<<<<\n";
  for (auto *OP : Frt.getUnresolvedPacks()) {
    OS << *OP << '\n';
    errs() << '\t';
    for (auto *V : *OP)
      errs() << (!V || (isa<Instruction>(V) && Frt.isFree(cast<Instruction>(V)))) << ' ';
    errs() << '\n';
  }
  OS << ">>>>>>>>>>>>>>>\n";
  OS << "UNRESOLVED SCALAR OPERANDS: <<<<<<<<<<<<\n";
  for (auto *V : Frt.getUnresolvedScalars())
    OS << V->getName() << ", ";
  OS << ">>>>>>>>>>>>>>>\n";
  return OS;
}

std::unique_ptr<Frontier>
Frontier::advance(const VectorPack *VP, float &Cost,
                  llvm::TargetTransformInfo *TTI) const {
  assert(Hash == computeHash(this));
  auto Next = std::make_unique<Frontier>(*this);
  Cost = Next->advanceInplace(VP, TTI);
  std::sort(Next->UnresolvedPacks.begin(), Next->UnresolvedPacks.end());
  assert(Next->Hash == computeHash(Next.get()));
  return Next;
}

std::unique_ptr<Frontier>
Frontier::advance(llvm::Instruction *I, float &Cost,
                  llvm::TargetTransformInfo *TTI) const {
  assert(Hash == computeHash(this));
  auto Next = std::make_unique<Frontier>(*this);
  Cost = Next->advanceInplace(I, TTI);
  std::sort(Next->UnresolvedPacks.begin(), Next->UnresolvedPacks.end());
  assert(Next->Hash == computeHash(Next.get()));
  return Next;
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

// Remove duplicate elements in OP
static const OperandPack *dedup(const VectorPackContext *VPCtx,
                                const OperandPack *OP) {
  if (!AggressivePacking)
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

extern VectorPack *tryCoalesceLoads(const VectorPack *MainPack,
                                    ArrayRef<const VectorPack *> OtherPacks,
                                    Packer *Pkr);

static std::vector<const VectorPack *>
findExtensionPacks(const Frontier &Frt, const CandidatePackSet *CandidateSet) {
  if (Frt.usableInstIds().count() == 0)
    return {};

  auto *Pkr = Frt.getPacker();
  auto *VPCtx = Frt.getContext();
  // Put load extensions in a separate category.
  // We don't extend with a load pack if we can extend with other arithmetic
  // packs
  std::vector<const VectorPack *> LoadExtensions;

  BitVector UnusableIds = Frt.usableInstIds();
  UnusableIds.flip();

  std::vector<const VectorPack *> Extensions;

  if (CandidateSet) {
    BitVector CandidateMembers = CandidateSet->Members;
    CandidateMembers &= Frt.usableInstIds();
    if (CandidateMembers.count()) {
      unsigned InstId = *CandidateMembers.set_bits_begin();
      //for (auto *VP : CandidateSet->Inst2Packs[InstId]) {
      for (auto *VP : CandidateSet->Packs) {
        auto &Elements = VP->getElements();
        if (/*Elements.test(InstId) &&*/ !Elements.anyCommon(UnusableIds))
          Extensions.push_back(VP);
      }
      ///////////
      for (auto *OP : Frt.getUnresolvedPacks()) {
        // if (!Extensions.empty())
        //  return Extensions;
        OP = dedup(VPCtx, OP);
        const OperandProducerInfo &OPI = Pkr->getProducerInfo(VPCtx, OP);
        for (auto *VP : OPI.Producers)
          if (!VP->getElements().anyCommon(UnusableIds) /*&&
              VP->getElements().test(InstId)*/)
            Extensions.push_back(VP);
        //for (auto *VP : OPI.LoadProducers)
        //  if (!VP->getElements().anyCommon(UnusableIds) &&
        //      VP->getElements().test(InstId))
        //    LoadExtensions.push_back(VP);
      }
      //////////
    }
    if (!Extensions.empty())
      return Extensions;
  }

  for (auto *OP : Frt.getUnresolvedPacks()) {
    if (!Extensions.empty())
      return Extensions;
    OP = dedup(VPCtx, OP);
    const OperandProducerInfo &OPI = Pkr->getProducerInfo(VPCtx, OP);
    if (!OPI.Feasible)
      continue;
    for (auto *VP : OPI.Producers)
      if (!VP->getElements().anyCommon(UnusableIds))
        Extensions.push_back(VP);
    for (auto *VP : OPI.LoadProducers)
      if (!VP->getElements().anyCommon(UnusableIds))
        LoadExtensions.push_back(VP);
  }

  // Delay extending with loads to create opportunity for coalescing loads
  if (!Extensions.empty())
    return Extensions;

  if (!LoadExtensions.empty()) {
    auto *LoadVP = LoadExtensions.front();
     if (auto *Coalesced = tryCoalesceLoads(
            LoadVP, ArrayRef<const VectorPack *>(LoadExtensions).slice(1),
            Pkr)) {
      return {Coalesced, LoadVP};
    }
    return {LoadVP};
  }
  return {};
}

template <typename AccessType>
VectorPack *createMemPack(VectorPackContext *VPCtx,
                          ArrayRef<AccessType *> Accesses,
                          const BitVector &Elements, const BitVector &Depended,
                          TargetTransformInfo *TTI);

template <>
VectorPack *createMemPack(VectorPackContext *VPCtx,
                          ArrayRef<StoreInst *> Stores,
                          const BitVector &Elements, const BitVector &Depended,
                          TargetTransformInfo *TTI) {
  return VPCtx->createStorePack(Stores, Elements, Depended, TTI);
}

template <>
VectorPack *createMemPack(VectorPackContext *VPCtx, ArrayRef<LoadInst *> Loads,
                          const BitVector &Elements, const BitVector &Depended,
                          TargetTransformInfo *TTI) {
  return VPCtx->createLoadPack(Loads, Elements, Depended, TTI);
}

template <typename AccessType>
std::vector<VectorPack *> getSeedMemPacks(Packer *Pkr, BasicBlock *BB,
                                          AccessType *Access, unsigned VL) {
  // if (!Frt.isUsable(Access)) {
  //  return {};
  //}
  auto &LDA = Pkr->getLDA(BB);
  auto *VPCtx = Pkr->getContext(BB);
  auto *TTI = Pkr->getTTI();
  bool IsStore = std::is_same<AccessType, StoreInst>::value;
  auto &AccessDAG = IsStore ? Pkr->getStoreDAG(BB) : Pkr->getLoadDAG(BB);

  std::vector<VectorPack *> Seeds;

  std::function<void(std::vector<AccessType *>, BitVector, BitVector)>
      Enumerate = [&](std::vector<AccessType *> Accesses, BitVector Elements,
                      BitVector Depended) {
        if (Accesses.size() == VL) {
          Seeds.push_back(createMemPack<AccessType>(VPCtx, Accesses, Elements,
                                                    Depended, TTI));
          return;
        }

        auto It = AccessDAG.find(Accesses.back());
        if (It == AccessDAG.end()) {
          return;
        }
        for (auto *Next : It->second) {
          auto *NextAccess = cast<AccessType>(Next);
          // if (!Frt.isUsable(NextAccess)) {
          //  continue;
          //}
          if (!checkIndependence(LDA, *VPCtx, NextAccess, Elements, Depended)) {
            continue;
          }
          auto AccessesExt = Accesses;
          auto ElementsExt = Elements;
          auto DependedExt = Depended;
          AccessesExt.push_back(NextAccess);
          ElementsExt.set(VPCtx->getScalarId(NextAccess));
          DependedExt |= LDA.getDepended(NextAccess);
          Enumerate(AccessesExt, ElementsExt, DependedExt);
        }
      };

  std::vector<AccessType *> Accesses{Access};
  BitVector Elements(VPCtx->getNumValues());
  BitVector Depended(VPCtx->getNumValues());

  Elements.set(VPCtx->getScalarId(Access));
  Depended |= LDA.getDepended(Access);

  Enumerate(Accesses, Elements, Depended);
  return Seeds;
}

static VectorPack *getSeedStorePack(const Frontier &Frt, StoreInst *SI,
                                    unsigned VL) {
  auto Seeds = getSeedMemPacks(Frt.getPacker(), Frt.getBasicBlock(), SI, VL);
  if (Seeds.empty())
    return nullptr;
  return Seeds[0];
}

class Aligner {
  BasicBlock *BB;
  const AccessLayoutInfo &LayoutInfo;
  DenseMap<std::pair<Instruction *, Instruction *>, float> AlignmentCache;

  // Alignment cost model
  static constexpr float MismatchCost = 1.0;
  static constexpr float ConstantCost = 0.0;
  static constexpr float SplatCost = 1.0;
  static constexpr float GatherCost = 1.0;
  static constexpr float MatchReward = -2.0;

public:
  Aligner(BasicBlock *BB, Packer *Pkr)
      : BB(BB), LayoutInfo(Pkr->getLoadInfo(BB)) {}
  float align(Instruction *I1, Instruction *I2) {
    if (I1->getParent() != BB || I2->getParent() != BB || isa<PHINode>(I1) ||
        isa<PHINode>(I2))
      return MismatchCost;
    auto It = AlignmentCache.find({I1, I2});
    if (It != AlignmentCache.end())
      return It->second;

    if (I1->getParent() != BB || I2->getParent() != BB)
      return MismatchCost;

    if (I1->getOpcode() != I2->getOpcode())
      return MismatchCost;

    // Special case for aligning a pair of loads: pay extra cost if the loads
    // are not adjacent
    auto *LI1 = dyn_cast<LoadInst>(I1);
    auto *LI2 = dyn_cast<LoadInst>(I2);
    if (LI1 && LI2) {
      if (LayoutInfo.isAdjacent(LI1, LI2))
        return MatchReward;
      auto Info1 = LayoutInfo.get(LI1);
      auto Info2 = LayoutInfo.get(LI2);
      if (Info1.Leader != Info2.Leader)
        return GatherCost;
      return 0.2 * std::abs(float(Info1.Id) - float(Info2.Id));
    }

    float Cost = MatchReward;
    for (unsigned i = 0, e = I1->getNumOperands(); i != e; i++) {
      Value *O1 = I1->getOperand(i);
      Value *O2 = I2->getOperand(i);
      auto *OI1 = dyn_cast<Instruction>(O1);
      auto *OI2 = dyn_cast<Instruction>(O2);
      if (isa<Constant>(O1) && isa<Constant>(O2)) {
        Cost += ConstantCost;
      } else if (OI1 && OI2) {
        Cost += align(OI1, OI2);
      } else if (O1 == O2) {
        Cost += SplatCost;
      } else {
        Cost += MismatchCost;
      }
    }
    return AlignmentCache[{I1, I2}] = Cost;
  }
};

bool usedByStore(Value *V) {
  for (User *U : V->users())
    if (auto *SI = dyn_cast<StoreInst>(U))
      return SI->getValueOperand() == V;
  return false;
}

struct AlignmentEdge {
  Instruction *Next;
  float Cost;
};

using EdgeSet = SmallVector<AlignmentEdge, 8>;
using AlignmentGraph = std::map<Instruction *, EdgeSet>;

// beam search
void enumerateImpl(std::vector<const OperandPack *> &Enumerated, Instruction *I,
                   VectorPackContext *VPCtx, const AlignmentGraph &AG,
                   unsigned BeamWidth, unsigned VL) {
  struct Candidate {
    OperandPack OP;
    float Cost = 0;

    Candidate extend(const AlignmentEdge &E) const {
      auto Ext = *this;
      Ext.OP.push_back(E.Next);
      Ext.Cost += E.Cost;
      return Ext;
    }
  };

  std::vector<Candidate> Candidates(1);
  Candidates.front().OP.push_back(I);

  for (unsigned i = 0; i < VL - 1; i++) {
    auto NextCandidates = Candidates;
    for (const auto &Cand : Candidates) {
      auto *LastI = cast<Instruction>(Cand.OP.back());
      auto It = AG.find(LastI);
      if (It == AG.end())
        continue;
      for (const AlignmentEdge &E : It->second)
        NextCandidates.push_back(Cand.extend(E));
    }
    Candidates.swap(NextCandidates);
    std::sort(
        Candidates.begin(), Candidates.end(),
        [](const Candidate &A, const Candidate &B) { return A.Cost < B.Cost; });
    Candidates.resize(std::min<unsigned>(Candidates.size(), BeamWidth));
  }

  for (auto &Cand : Candidates)
    if (Cand.OP.size() == VL) {
      Enumerated.push_back(VPCtx->getCanonicalOperandPack(Cand.OP));
    }
}

std::vector<const VectorPack *> enumerate(BasicBlock *BB, Packer *Pkr) {
  auto &LDA = Pkr->getLDA(BB);
  auto *VPCtx = Pkr->getContext(BB);
  Aligner A(BB, Pkr);
  Metricizer<AffineEmbedder> Metric(AffineEmbedder(BB, Pkr->getDataLayout()));
  auto &LayoutInfo = Pkr->getStoreInfo(BB);

  AlignmentGraph AG;
  for (auto &I : *BB) {
#if 0
    if (auto *SI = dyn_cast<StoreInst>(&I)) {
      auto Info = LayoutInfo.get(SI);
      if (Info.Id == 0) {
        for (auto *VP : getSeedMemPacks(Pkr, BB, SI, 16)) {
          auto *OP = VP->getOperandPacks()[0];
          errs() << "SIMILARITY MATRIX:\n";
          for (auto *V1 : *OP) {
            for (auto *V2 : *OP) {
              errs() << (A.align(cast<Instruction>(V1), cast<Instruction>(V2)) /*< 10*/) << ' ';
            }
            errs() << '\n';
          }
          abort();
        }
      }
    }
#endif

    if (!usedByStore(&I))
      continue;
    auto Independent = LDA.getIndependent(&I);
    for (auto &J : *BB) {
      if (&I == &J)
        continue;
      if (!usedByStore(&J))
        continue;
      if (!Independent.test(VPCtx->getScalarId(&J)))
        continue;
      //bool Close = Metric.getDistance(&I, &J) < 1;
      bool Close = A.align(&I, &J) < 0;
      if (Close) {
        errs() << "ALIGNED " << I << ", " << J << ", COST = " << A.align(&I, &J) << '\n';
        AG[&I].push_back({&J, A.align(&I, &J)});
      }
    }
  }

  unsigned NumCands = 0;
  std::vector<const OperandPack *> Enumerated;
  for (auto &I : *BB) {
    if (!usedByStore(&I))
      continue;
    unsigned OldSize = Enumerated.size();
    //if (UseMCTS) {
      //enumerateImpl(Enumerated, &I, VPCtx, AG, 64/*beam width*/, 2 /*VL*/);
      enumerateImpl(Enumerated, &I, VPCtx, AG, 64/*beam width*/, 4 /*VL*/);
      enumerateImpl(Enumerated, &I, VPCtx, AG, 64/*beam width*/, 8 /*VL*/);
      enumerateImpl(Enumerated, &I, VPCtx, AG, 64/*beam width*/, 16 /*VL*/);
    //}
    for (unsigned i = OldSize; i < Enumerated.size(); i++)
     errs() << "!!! candidate: " << *Enumerated[i] << '\n';
  }
#if 0
  {
      auto X = Enumerated;
      for (auto *OP : Enumerated) {
        for (auto *OP2 : Enumerated) {
          if (OP == OP2)
            continue;
          if (OP->size() != 8 || OP2->size() != 8)
            continue;
          OperandPack Concat = *OP;
          for (auto *V : *OP2)
            Concat.push_back(V);
          X.push_back(VPCtx->getCanonicalOperandPack(Concat));
        }
      }
      Enumerated = X;
  }
#endif

  // errs() << "!!! num candidates: " << Enumerated.size() << '\n';

  std::vector<const VectorPack *> Packs;
  for (auto *OP : Enumerated) {
    auto &OPI = Pkr->getProducerInfo(VPCtx, OP);
    for (auto *VP : OPI.Producers)
      Packs.push_back(VP);
  }

  for (auto &I : *BB) {
    if (auto *LI = dyn_cast<LoadInst>(&I)) {
      for (unsigned VL : {2, 4, 8, 16, 32, 64})
        for (auto *VP : getSeedMemPacks(Pkr, BB, LI, VL))
          Packs.push_back(VP);
    }
  }
  for (auto &I : *BB) {
    if (auto *LI = dyn_cast<StoreInst>(&I)) {
      for (unsigned VL : {2, 4, 8, 16, 32, 64})
        for (auto *VP : getSeedMemPacks(Pkr, BB, LI, VL))
          Packs.push_back(VP);
    }
  }
  return Packs;
}

static OperandPack *buildOperandPack(const VectorPackContext *VPCtx,
                                     const BitVector &Elements) {
  OperandPack OP;
  for (unsigned i : Elements.set_bits())
    OP.push_back(VPCtx->getScalar(i));
  return VPCtx->getCanonicalOperandPack(OP);
}

// Fill out the children node
void UCTNode::expand(const CandidatePackSet *CandidateSet) {
  assert(Transitions.empty() && "expanded already");
  auto *Pkr = getPacker();

  auto *BB = Frt->getBasicBlock();

  bool CanExpandWithStore = false;

  for (auto *V : Frt->usableInsts()) {
    // Consider seed packs
    if (auto *SI = dyn_cast<StoreInst>(V)) {
      // for (unsigned VL : {2, 4, 8, 16, 32, 64}) {
      for (unsigned VL : {2, 4, 8, 16}) {
        if (auto *VP = getSeedStorePack(*Frt, SI, VL)) {
          CanExpandWithStore = true;
          Transitions.emplace_back(VP);
        }
      }

      if (CanExpandWithStore) {
        Transitions.emplace_back(SI);
        break;
      }
    }
  }

  if (CanExpandWithStore)
    return;

  auto Extensions = findExtensionPacks(*Frt, CandidateSet);
  // Also consider the extension packs
  for (auto *VP : Extensions)
    Transitions.emplace_back(VP);

  if (Transitions.empty()) {
    for (auto *V : Frt->usableInsts()) {
      auto *I = dyn_cast<Instruction>(V);
      if (!I)
        continue;

      // Consider scalars
      Transitions.emplace_back(I);
    }
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
      CurNode = BestT->getNext(CurNode, Factory, TTI);
    }

    float LeafCost = 0;
    // ========= 2) Expansion ==========
    if (!CurNode->isTerminal()) {
      // ======= 3) Evaluation/Simulation =======
      LeafCost = evalLeafNode(CurNode);
      if (CurNode->visitCount() >= ExpandThreshold) {
        CurNode->expand(CandidateSet);
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

float makeOperandPacksUsable(Frontier &Frt, CandidatePackSet *Candidates=nullptr) {
  auto *Pkr = Frt.getPacker();
  auto *TTI = Pkr->getTTI();
  auto *BB = Frt.getBasicBlock();
  auto *VPCtx = Frt.getContext();

  float Cost = 0;

  BitVector VectorOperandSet(VPCtx->getNumValues());
  for (auto *OP : Frt.getUnresolvedPacks())
    VectorOperandSet |= Pkr->getProducerInfo(VPCtx, OP).Elements;
  if (Candidates)
    VectorOperandSet |= Candidates->Members;

  bool Changed;
  do {
    Changed = false;
    const BitVector &UsableIds = Frt.usableInstIds();
    for (auto It = UsableIds.set_bits_begin(), E = UsableIds.set_bits_end();
         It != E; ++It) {
      if (VectorOperandSet.test(*It))
        continue;
      if (auto *I = dyn_cast<Instruction>(VPCtx->getScalar(*It))) {
        Cost += Frt.advanceInplace(I, TTI);
        Changed = true;
      }
    }
  } while (Changed);
  return Cost;
}

float UCTSearch::evalLeafNode(UCTNode *N) {
  return Evaluator->evaluate(N->getFrontier(), CandidateSet);
}

std::unique_ptr<Heuristic> H;

// Uniformly random rollout
float RolloutEvaluator::evaluate(const Frontier *Frt,
                                 const CandidatePackSet *CandidateSet) {
  return H->getCost(Frt);
  auto *Pkr = Frt->getPacker();
  auto *TTI = Pkr->getTTI();
  auto *BB = Frt->getBasicBlock();
  auto *VPCtx = Frt->getContext();
  auto ScratchFrt = *Frt;

  BitVector VectorOperandSet(VPCtx->getNumValues());
  for (auto *OP : ScratchFrt.getUnresolvedPacks())
    VectorOperandSet |= Pkr->getProducerInfo(VPCtx, OP).Elements;

  BitVector NonFree(VPCtx->getNumValues());

  float Cost = 0;
  bool Changed;
  std::vector<const VectorPack *> Extensions;
  do {
    Changed = false;
    Extensions = findExtensionPacks(ScratchFrt, CandidateSet);
    while (!Extensions.empty()) {
      auto *VP = Extensions[rand_int(Extensions.size())];
      Cost += ScratchFrt.advanceInplace(VP, TTI);
      Extensions = findExtensionPacks(ScratchFrt, CandidateSet);

      for (auto *OP : VP->getOperandPacks())
        VectorOperandSet |= Pkr->getProducerInfo(VPCtx, OP).Elements;
      NonFree = ScratchFrt.getFreeInsts();
      NonFree.flip();
      VectorOperandSet &= NonFree;

      Changed = true;
    }

#if 0
    for (auto *OP : ScratchFrt.getUnresolvedPacks()) {
      auto *VecTy = getVectorType(*OP);
      for (unsigned i = 0; i < OP->size(); i++) {
        auto *V = (*OP)[i];
        if (!V) continue;
        auto *I = dyn_cast<Instruction>(V);
        if (!I || I->getParent() != BB || ScratchFrt.isUsable(I))
          continue;
        ScratchFrt.markInstUsable(VPCtx->getScalarId(I));
        Cost += TTI->getVectorInstrCost(Instruction::ExtractElement, VecTy, i);
        //errs() << "!!! paying extract cost for " << *OP << " at index " << i << '\n'; 
        Changed = true;
      }
    }
#else
    const BitVector &UsableIds = ScratchFrt.usableInstIds();
    for (auto It = UsableIds.set_bits_begin(), E = UsableIds.set_bits_end();
         It != E; ++It) {
      if (VectorOperandSet.test(*It))
        continue;
      if (auto *I = dyn_cast<Instruction>(VPCtx->getScalar(*It))) {
        Changed = true;
        auto *SI = dyn_cast<StoreInst>(I);
        if (SI && rand_int(4)) {
          std::vector<const VectorPack *> Seeds;
          for (unsigned i : {2, 4, 8, 16}) {
            // for (unsigned i : {8}) {
            auto *SeedVP = getSeedStorePack(ScratchFrt, SI, i);
            if (SeedVP)
              Seeds.push_back(SeedVP);
          }
          if (unsigned N = Seeds.size()) {
            Cost += ScratchFrt.advanceInplace(Seeds[rand_int(N)], TTI);
            break;
          }
        }

        Cost += ScratchFrt.advanceInplace(I, TTI);
      }
    }
#endif
  } while (Changed && !ScratchFrt.getUnresolvedPacks().empty());

  return Cost + estimateAllScalarCost(ScratchFrt, TTI);
}

class DPSolver {
  const CandidatePackSet *CandidateSet;
  struct Solution {
    float Cost;
    const VectorPack *VP;
    bool Fill;

    // Default solution is no extension
    Solution() = default;
    Solution(float Cost, VectorPack *VP) : Cost(Cost), VP(VP), Fill(false) {}
    Solution(float Cost) : Cost(Cost), VP(nullptr), Fill(true) {}
  };
  TargetTransformInfo *TTI;

  DenseMap<const Frontier *, Solution, FrontierHashInfo> Solutions;
  std::vector<std::unique_ptr<Frontier>> Frontiers;

  Solution solveImpl(const Frontier &Frt) {
    // Figure out the cost of not adding any extensions.
    Solution Sol;
    Sol.VP = nullptr;
    Sol.Fill = false;
    Sol.Cost = 0;
    Sol.Cost = estimateAllScalarCost(Frt, TTI);

    // Figure out the cost of adding one extension
    auto Extensions = findExtensionPacks(Frt, CandidateSet);
    // errs() << "NUM EXTENSIONS: " << Extensions.size() << '\n';
    for (const VectorPack *ExtVP : Extensions) {
      float LocalCost;
      auto NextFrt = Frt.advance(ExtVP, LocalCost, TTI);
      float TotalCost = solve(std::move(NextFrt)).Cost + LocalCost;
      // errs() << " EXTENDING WITH " << *ExtVP
      //       << ", transition cost : " << LocalCost
      //       << ", local cost : " << ExtVP->getCost()
      //       << ", total cost : " << TotalCost
      //       << ", num elems: " << ExtVP->getOrderedValues().size()
      //       << ", best cost so far: " << Sol.Cost << '\n';

      if (Sol.Cost > TotalCost) {
        Sol.Cost = TotalCost;
        Sol.VP = ExtVP;
        Sol.Fill = false;
      }
    }

    if (Extensions.empty()) {
      auto ScratchFrt = Frt;
      float FillCost = makeOperandPacksUsable(ScratchFrt);
      if (findExtensionPacks(ScratchFrt).empty()) {
        return Sol;
      } else {
        float TotalCost = solve(ScratchFrt).Cost + FillCost;
        if (Sol.Cost > TotalCost) {
          Sol.Cost = TotalCost;
          Sol.VP = nullptr;
          Sol.Fill = true;
        }
      }
    }

    return Sol;
  }

public:
  DPSolver(TargetTransformInfo *TTI,
           const CandidatePackSet *CandidateSet = nullptr)
      : CandidateSet(CandidateSet), TTI(TTI), Solutions(1000000) {}

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

float astar(VectorPackSet &Packs, Frontier *Frt, Packer *Pkr, BasicBlock *BB,
            CandidatePackSet *Candidates) {
  auto *VPCtx = Pkr->getContext(BB);
  Heuristic H(Pkr, VPCtx, Candidates);
  struct Data {
    // Edge
    const VectorPack *VP;
    const Frontier *Prev;
    float Cost;
    float TransitionCost;
    bool Visited;
    // Data(const VectorPack *VP, const Frontier *Prev, float Cost,
    //    float TransitionCost)
    //  : VP(VP), Prev(Prev), Cost(Cost), TransitionCost(TransitionCost) {}
  };
  std::vector<std::unique_ptr<Frontier>> Frontiers;

  struct HeapEntry {
    const Frontier *Frt;
    float Key;

    // std::priority_queue implements a max heap
    bool operator<(const HeapEntry &Other) const { return Key < Other.Key; }
  };

  std::priority_queue<HeapEntry> Queue;
  float BestCost = -1;
  DenseMap<const Frontier *, Data, FrontierHashInfo> NodeData;
  auto Push = [&](const Frontier *PrevFrt, const Frontier *Frt, float Cost,
                  float TransitionCost, const VectorPack *VP) {
    auto It = NodeData.find(Frt);
    if (It == NodeData.end() || It->second.Cost > Cost) {
      errs() << "!!! g: " << Cost << ", h: " << H.getCost(Frt) << " est: "
             << Cost + H.getCost(Frt)
             //<< *Frt
             << '\n';
      float Key;
      if (BestCost > 0) {
        Key = (BestCost - Cost) / H.getCost(Frt);
      } else {
        Key = -H.getCost(Frt);
      }
      if (It == NodeData.end()) {
        NodeData[Frt] = {VP, PrevFrt, Cost, TransitionCost, false};
        if (BestCost > 0 && Cost + H.getCost(Frt) > BestCost)
          return;
        Queue.push({Frt, Key});
      } else {
        It->second = {VP, PrevFrt, Cost, TransitionCost, false};
        if (BestCost > 0 && Cost + H.getCost(Frt) > BestCost)
          return;
        Queue.push({It->first, Key});
      }
    }
  };

  NodeData[Frt] = {nullptr, nullptr, 1 /*inf*/, false /*visied?*/};
  Push(nullptr, Frt, 0, 0, nullptr);

  auto *TTI = Pkr->getTTI();

  const Frontier *Final;
  while (!Queue.empty()) {
    while (!Queue.empty()) {
      auto It = NodeData.find(Queue.top().Frt);
      assert(It != NodeData.end());
      float FrtCost = It->second.Cost;
      // Get the canonical frontier
      auto *Frt = It->first;
      errs() << "!!! " << Frt << '\n';
      Queue.pop();
      if (It->second.Visited)
        continue;
      errs() << "~~~~ " << Queue.size() << '\n';
      It->second.Visited = true;
      //errs() << "!!! " << Frt->getFreeInsts().count() << '\n';

      if (Frt->numUsableInsts() == 0) {
        errs() << "Final queue size: " << Queue.size() << '\n';
        Final = Frt;
        break;
      }

      // 1) add a pack
      BitVector UnusableIds = Frt->usableInstIds();
      UnusableIds.flip();

      //// WHY DOES THIS MATTER/???????? figure it out
#if 0
      std::vector<unsigned> ids;
      for (unsigned i : Frt->usableInstIds().set_bits())
        ids.push_back(i);
      unsigned InstId = ids[ids.size()-1];
      //unsigned InstId; = *Frt->usableInstIds().set_bits_begin();
      std::vector<const VectorPack *> VPs = Candidates->Inst2Packs[InstId];
      for (auto *OP : Frt->getUnresolvedPacks()) {
        OP = dedup(VPCtx, OP);
        auto &OPI = Pkr->getProducerInfo(VPCtx, OP);
        if (!OPI.Elements.test(InstId))
          continue;
        for (auto *VP : OPI.Producers)
          VPs.push_back(VP);
      }
#else
      unsigned InstId = *Frt->usableInstIds().set_bits_begin();
      auto VPs = findExtensionPacks(*Frt, Candidates);
#endif
      for (auto *VP : VPs) {
        if (VP->getElements().anyCommon(UnusableIds))
          continue;
        float Cost;
        Frontiers.push_back(Frt->advance(VP, Cost, TTI));
        // We count the total instruction cost instead of the net saving.
        //errs() << "!! " << *VP << '\n';
        Push(Frt, Frontiers.back().get(),
            FrtCost + Cost /*- VP->getCost() + VP->getProducingCost()*/, Cost,
            VP);
      }
      //errs() << "num extension packs: " << VPs.size() << '\n';
      //auto *I = cast<Instruction>(VPCtx->getScalar(InstId));
      //float Cost;
      //Frontiers.push_back(Frt->advance(I, Cost, TTI));
      ////errs() << "!! " << *I << '\n';
      //Push(Frt, Frontiers.back().get(),
      //     FrtCost + Cost /* + Pkr->getScalarCost(I)*/, Cost, nullptr);

      // 2) scalarize
      if (VPs.empty()) {
        //for (auto *V : Frt->usableInsts()) {
        //  auto *I = dyn_cast<Instruction>(V);
        //  // 1) fix I as scalar.
        //  float Cost;
        //  Frontiers.push_back(Frt->advance(I, Cost, TTI));
        //  //errs() << "!! " << *I << '\n';
        //  Push(Frt, Frontiers.back().get(),
        //       FrtCost + Cost /* + Pkr->getScalarCost(I)*/, Cost, nullptr);
        //}
        auto ScratchFrt = std::make_unique<Frontier>(*Frt);
        float Cost = makeOperandPacksUsable(*ScratchFrt, Candidates);
        Frontiers.push_back(std::move(ScratchFrt));
        Push(Frt, Frontiers.back().get(),
            FrtCost + Cost /* + Pkr->getScalarCost(I)*/, Cost, nullptr);

        //for (auto *V : Frt->usableInsts()) {
        //  auto *I = dyn_cast<Instruction>(V);
        //  // 1) fix I as scalar.
        //  float Cost;
        //  Frontiers.push_back(Frt->advance(I, Cost, TTI));
        //  errs() << "!! " << *I << '\n';
        //  Push(Frt, Frontiers.back().get(),
        //      FrtCost + Cost /* + Pkr->getScalarCost(I)*/, Cost, nullptr);
        //}
      }
      if (Queue.empty()) {
      for (auto *V : Frt->usableInsts()) {
        auto *I = dyn_cast<Instruction>(V);
        // 1) fix I as scalar.
        float Cost;
        Frontiers.push_back(Frt->advance(I, Cost, TTI));
        //errs() << "!! " << *I << '\n';
        Push(Frt, Frontiers.back().get(),
             FrtCost + Cost /* + Pkr->getScalarCost(I)*/, Cost, nullptr);
      }
      }
    }


    const Frontier *CurFrt = Final;
    float NetSaving = 0;
    while (CurFrt) {
      auto &X = NodeData[CurFrt];
      if (auto *VP = X.VP)
        Packs.tryAdd(VP);
      CurFrt = X.Prev;
      NetSaving += X.TransitionCost;
    }

    BestCost = NetSaving;
    errs() << "!!! best cost so far: " << NetSaving << '\n';

    //if (NetSaving == 91)
    //  break;

    decltype(Queue) NewQueue;
    while (!Queue.empty()) {
      HeapEntry Entry = Queue.top();
      Queue.pop();

      if (NodeData[Entry.Frt].Cost + H.getCost(Entry.Frt) >= BestCost)
        continue;

      Entry.Key = (BestCost - NodeData[Entry.Frt].Cost) / H.getCost(Entry.Frt);
      NewQueue.push(Entry);
    }
    errs() << Queue.size() << ", " << NewQueue.size() << '\n';
    Queue.swap(NewQueue);
  }

  // back trace to find the pack set
  assert(Final);
  const Frontier *CurFrt = Final;
  float NetSaving = 0;
  while (CurFrt) {
    auto &X = NodeData[CurFrt];
    if (auto *VP = X.VP)
      Packs.tryAdd(VP);
    CurFrt = X.Prev;
    NetSaving += X.TransitionCost;
  }
  return NetSaving;
}

struct PackingInfo {
  const VectorPack *VP;
  float Saving; // net saving
};

std::vector<const VectorPack *> selectPacks(ArrayRef<PackingInfo> Infos) {
  std::vector<const VectorPack *> Selected;
  BitVector Selectable(Infos.size(), true);
  std::vector<BitVector> ConflictGraph;
  for (unsigned i = 0; i < Infos.size(); i++) {
    BitVector Conflicted(Infos.size());
    for (unsigned j = 0; j < Infos.size(); j++) {
      if (Infos[i].VP->getElements().anyCommon(Infos[j].VP->getElements()))
        Conflicted.set(j);
    }
    ConflictGraph.push_back(Conflicted);
  }

  std::vector<float> AvgNeighborSavings;
  auto RecomputeNeighborSaving = [&]() {
    AvgNeighborSavings.clear();
    for (unsigned i = 0; i < Infos.size(); i++) {
      float TotalSaving = 0;
      float NumNeighbors = 0;
      auto AliveNeighbors = ConflictGraph[i];
      AliveNeighbors &= Selectable;
      for (unsigned j : AliveNeighbors.set_bits()) {
        TotalSaving += Infos[j].Saving;
        NumNeighbors += 1;
      };
      float Avg = NumNeighbors > 0 ?  (TotalSaving / NumNeighbors) : 1e16;
      AvgNeighborSavings.push_back(Avg);
    }
  };


  while (Selectable.count()) {
    RecomputeNeighborSaving();
    int MaxId = -1;
    for (unsigned i : Selectable.set_bits()) {
      if (MaxId == -1 || AvgNeighborSavings[MaxId] < AvgNeighborSavings[i])
        MaxId = i;
    }
    errs() << "??????? " << MaxId << '\n';
    Selectable.reset(MaxId);
    Selected.push_back(Infos[MaxId].VP);
    for (unsigned i : Selectable.set_bits()) {
      if (ConflictGraph[i].test(MaxId))
        Selectable.reset(i);
    }
  }

  return Selected;
}

float optimizeBottomUp(VectorPackSet &Packs, Packer *Pkr, BasicBlock *BB) {
  Frontier Frt(BB, Pkr);

  CandidatePackSet CandidateSet;
  CandidateSet.Packs = enumerate(BB, Pkr);
  auto *VPCtx = Frt.getContext();
  CandidateSet.Members = BitVector(VPCtx->getNumValues());
  CandidateSet.Inst2Packs.resize(VPCtx->getNumValues());
  for (auto *VP : CandidateSet.Packs) {
    CandidateSet.Members |= VP->getElements();
    for (unsigned i : VP->getElements().set_bits())
      CandidateSet.Inst2Packs[i].push_back(VP);
  }

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

  // errs() << "??? num stores: " << Stores.size() << '\n';

  auto *TTI = Pkr->getTTI();

  DPSolver Solver(TTI, AggressivePacking ? &CandidateSet : nullptr);

  std::vector<unsigned> VL{64, 32, 16, 8, 4, 2};
  // std::vector<unsigned> VL{16, 8, 4, 2};
  // VL = {8};
  // VL = {4};
  // VL = {64};
  // VL = {64};
  //VL = {4};
  //VL = {16};
  VL = { 8 };
  VL = { 2 };
  float Cost = 0;
  float BestEst = 0;

  if (!UseMCTS || true) {
  //if (false) {
    for (unsigned i : VL) {
      for (auto *SI : Stores) {
        auto *SeedVP = getSeedStorePack(Frt, SI, i);
        if (SeedVP) {
          auto Frozen = Frt.getFreeInsts();
          Frozen.flip();
          if (Frozen.anyCommon(SeedVP->getElements()))
            continue;
          Cost += Frt.advanceInplace(SeedVP, TTI);
          Packs.tryAdd(SeedVP);
          continue;
#if 0
          float Est = estimateCost(Frt, SeedVP);
#else
          float LocalCost;
          auto Sol = Solver.solve(Frt.advance(SeedVP, LocalCost, TTI));
          float Est = LocalCost + Sol.Cost;
          auto *OP = SeedVP->getOperandPacks()[0];
          auto &OPI = Pkr->getProducerInfo(VPCtx, OP);
#endif
          if (Est < BestEst) {
#if 0
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
              // errs() << "????\n";
              auto Sol = Solver.solve(Frt);
              if (auto *ExtVP = Sol.VP) {
                // errs() << "Adding pack " << *ExtVP << '\n';
                Cost += Frt.advanceInplace(ExtVP, TTI);
                // errs() << "NEW COST: " << Cost << '\n';
                Packs.tryAdd(ExtVP);
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
  }

  // try out the new heuristic
#if 0
  {
  struct Transition {
    std::unique_ptr<Frontier> Frt;
    float Cost;
    const VectorPack *VP;
    Instruction *I;
  };
  Heuristic H(Pkr, VPCtx, &CandidateSet);
  auto CurFrt = std::make_unique<Frontier>(Frt);
  bool Selected = false;
  while (CurFrt->numUsableInsts()) {
    auto Extensions = findExtensionPacks(*CurFrt, &CandidateSet);
    std::vector<Transition> Transitions;
    std::vector<float> Costs;
    std::vector<PackingInfo> Infos;
    for (auto *VP : Extensions) {
      float Cost;
      auto Next = CurFrt->advance(VP, Cost, TTI);
      Costs.push_back(Cost + H.getCost(Next.get()));
      Transitions.push_back(Transition{std::move(Next), Cost, VP, nullptr});
#if 0
      if (H.getSaving(VP) - Cost > 0)
        Infos.push_back(PackingInfo{VP, H.getSaving(VP) - Cost});
#endif
    }

#if 0
    if (!Selected) {
      for (auto *VP : selectPacks(Infos)) {
        errs() << "SELECTED " << *VP << '\n';
        Cost += CurFrt->advanceInplace(VP, TTI);
        Packs.tryAdd(VP);
        Selected = true;
      }
      if (Selected) {
        //Selected= false;
        continue;
      }
    }
#endif

    if (Transitions.empty()) {
      //float Cost2 = makeOperandPacksUsable(*CurFrt);
      //Cost += Cost2;
      //if (Cost2 != 0)
      //  continue;
      errs() << ":( STUCK " << *CurFrt << '\n';
      for (auto *V : CurFrt->usableInsts()) {
        //if (CandidateSet.Members.test(VPCtx->getScalarId(V)))
        //  continue;
        auto *I = cast<Instruction>(V);
        float Cost;
        auto Next = CurFrt->advance(I, Cost, TTI);
        Costs.push_back(Cost + H.getCost(Next.get()));
        Transitions.push_back(Transition{std::move(Next), Cost, nullptr, I});
      }
    }
    // FIXME: this is broken when you consider the constraint that one instruction belongs to only one pack.
    unsigned MinId = std::min_element(Costs.begin(), Costs.end()) - Costs.begin();
    auto &T = Transitions[MinId];
    if (T.VP) {
      Packs.tryAdd(T.VP);
      errs() << "!!!!!! adding " << *T.VP << '\n';
      errs() << "estimated total scalar saving: " << H.getSaving(T.VP) << '\n';
    } else {
      errs() << "!!! scalarizing " << *T.I << '\n';
    }
    Cost += T.Cost;
    CurFrt = std::move(T.Frt);
  }
  return Cost;
  }
#else
  //return astar(Packs, &Frt, Pkr, BB, &CandidateSet);
#endif
  H = std::make_unique<Heuristic>(Pkr, VPCtx, &CandidateSet);

  //if (UseMCTS || true) {
  if (false) {
    UCTNodeFactory Factory;
    RolloutEvaluator Evaluator;
    UCTSearch MCTS(0.1 /*c*/, 0.0 /*w*/, 0 /*ExpandThreshold*/, &Factory, Pkr,
                   nullptr /*Policy*/, &Evaluator, &CandidateSet, TTI);
    UCTNode *Root = Factory.getNode(std::make_unique<Frontier>(Frt));
    unsigned NumSimulations = 10000;
    float TotalCost = 0;
    Root->expand(&CandidateSet);

    while (!Root->isTerminal()) {
      MCTS.run(Root, NumSimulations);
      assert(Root->expanded());

      if (Root->transitions().empty())
        break;

      auto &Transitions = Root->transitions();
      errs() << "NUM TRANSITIONS : " << Transitions.size() << '\n';

      UCTNode::Transition *T = &*std::max_element(
          Transitions.begin(), Transitions.end(),

          [](const UCTNode::Transition &A, const UCTNode::Transition &B) {
         // return A.Count < B.Count;
            float ACost = -A.Cost - A.Next->minCost();
            float BCost = -B.Cost - B.Next->minCost();
            return std::tie(ACost, A.Count) < std::tie(BCost, B.Count);
          });

      auto Node = Root;
      auto *Next = T->getNext(Node, &Factory, TTI);
      errs() << "====================================="
             << "\n\t t transition cost: " << T->transitionCost()
             << "\n\t num transitions: " << Transitions.size()
             << "\n\t scalar cost: " << Transitions.begin()->avgCost()
             << "\n\t t avg cost: " << T->avgCost()
             << "\n\t t->next avg cost: " << Next->avgCost()
             << "\n\t t->next min cost: " << Next->minCost()
             << "\n\t t->next terminal? " << Next->isTerminal()
             << "\n\t t visit count : " << T->visitCount()
             << "\n\t node visit count: " << Node->visitCount()
             << "\n\t min cost : " << Node->minCost()
             << "\n\t max cost : " << Node->maxCost()
             << "\n\t avg cost : " << Node->avgCost()
             << "\n\t score : " << Node->score(*T, 0)
             << "\n\t num unresolved packs : "
             << Node->getFrontier()->getUnresolvedPacks().size()
             << "\n\t num unresolved scalars : "
             << Node->getFrontier()->numUnresolvedScalars() << '\n';

      if (T->VP) {
        errs() << "[MCTS] ADDING: " << *T->VP << '\n';
        Packs.tryAdd(T->VP);
      } else if (T->I) {
        errs() << "[MCTS] Scalarizing: " << *T->I << '\n';
      }
      Root = T->getNext(Root, &Factory, TTI);
      TotalCost += T->transitionCost();
      errs() << "[MCTS] New cost: " << TotalCost << '\n';
      errs() << *Root->getFrontier() << '\n';
    }
  } else {
    for (;;) {
#if 0
      auto *ExtVP = findExtensionPack(Frt);
#else
      auto Sol = Solver.solve(Frt);
#endif

      if (auto *ExtVP = Sol.VP) {
        Cost += Frt.advanceInplace(ExtVP, TTI);
        Packs.tryAdd(ExtVP);
      } else if (Sol.Fill) {
        Cost += makeOperandPacksUsable(Frt);
      } else {
        break;
      }
      // errs() << "!!! Adding : " << *ExtVP << '\n';
      // errs() << "\t updated cost: " << Cost << '\n';
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
  }

  return Cost;
}
