#include "Solver.h"
#include "Heuristic.h"
#include "MatchManager.h"
#include "VectorPackSet.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Timer.h"

using namespace llvm;

static cl::opt<bool> UseTimer("use-timer", cl::desc("use timer"));

Frontier::Frontier(BasicBlock *BB, Packer *Pkr)
    : Pkr(Pkr), BB(BB), VPCtx(Pkr->getContext(BB)),
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
        if (UserInst->getParent() != BB) {
          // Mark that `I` has a scalar use.
          if (UnresolvedScalars.test(InstId)) {
            UnresolvedScalars.set(InstId);
          }
        } else
          // `I` is used by some other instruction in `BB`
          AllUsersResolved = false;
      }
    }

    if (AllUsersResolved || isa<PHINode>(&I))
      UsableInsts.set(InstId);
  }
}

void Frontier::freezeOneInst(Instruction *I) {
  unsigned InstId = VPCtx->getScalarId(I);
  // assert(FreeInsts.test(InstId));
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

bool Frontier::resolved(const OperandPack &OP) const {
  return !Pkr->getProducerInfo(VPCtx, &OP).Elements.anyCommon(FreeInsts);
}

float Frontier::advanceInplace(Instruction *I, TargetTransformInfo *TTI) {
  NamedRegionTimer Timer("advance/i", "advance with instruction ",
                         "pack selection", "", UseTimer);
  // float Cost = 0;
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
    }
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

  return 2; // 0.5;
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
  NamedRegionTimer Timer("advance/pack", "advance with pack", "pack selection",
                         "", UseTimer);
  // float Cost = VP->getCost();
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
        UnresolvedPacks.push_back(OpndPack);
      }
    }
  }

  remove(UnresolvedPacks, ResolvedPackIds);
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

raw_ostream &operator<<(raw_ostream &OS, const Frontier &Frt) {
  OS << "============== FRONTIER STATE ==========\n";
  OS << "UNRESOLVED VECTOR OPERANDS: <<<<<<<<<<<<<<<<<<<<<<\n";
  for (auto *OP : Frt.getUnresolvedPacks()) {
    OS << *OP << '\n';
    errs() << '\t';
    for (auto *V : *OP)
      errs() << (!V ||
                 (isa<Instruction>(V) && Frt.isFree(cast<Instruction>(V))))
             << ' ';
    errs() << '\n';
  }
  OS << ">>>>>>>>>>>>>>>\n";
  OS << "UNRESOLVED SCALAR OPERANDS: <<<<<<<<<<<<\n";
  for (auto *V : Frt.getUnresolvedScalars())
    OS << V->getName() << ", ";
  OS << ">>>>>>>>>>>>>>>\n";
  return OS;
}

// Remove duplicate elements in OP
static const OperandPack *dedup(const VectorPackContext *VPCtx,
                                const OperandPack *OP) {
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
                             ArrayRef<const VectorPack *> OtherPacks, Packer *Pkr) {
  auto *BB = MainPack->getBasicBlock();
  auto &LayoutInfo = Pkr->getLoadInfo(BB);
#if 0
  // Full, can't coalesce
  if (MainPack->getOrderedValues().size() == MainPack->getElements().count())
    return nullptr;
#endif

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
    auto Info =
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
      if (!Ok) {
        Coalesced = false;
        break;
      }
    }
    if (Coalesced && Temp.utilization() >= Slots.utilization()) {
      Slots = Temp;
      Depended |= Other->getDepended();
      Elements |= Other->getElements();
    }
  }

  if (Elements == MainPack->getElements())
    return nullptr;

  std::vector<LoadInst *> Loads;
  for (unsigned i = Slots.minId(), e = Slots.maxId(); i <= e; i++) {
    Loads.push_back(Slots[i]);
  }

  return Pkr->getContext(BB)->createLoadPack(Loads, Elements, Depended,
                                             Pkr->getTTI());
}

static std::vector<const VectorPack *>
findExtensionPacks(const Frontier &Frt, const CandidatePackSet *CandidateSet) {
  NamedRegionTimer Timer("find-extensions", "find extensions", "pack selection",
                         "", UseTimer);
  if (Frt.usableInstIds().count() == 0)
    return {};

  auto *Pkr = Frt.getPacker();
  auto *VPCtx = Frt.getContext();

  BitVector UnusableIds = Frt.usableInstIds();
  UnusableIds.flip();

  BitVector Covered(VPCtx->getNumValues());
  std::vector<const VectorPack *> Extensions;
  // Consider VP as an extension
  auto Consider = [&](const VectorPack *VP) {
    auto &Elements = VP->getElements();
    if (Elements.anyCommon(UnusableIds))
      return;
    if (!Covered.count() || Elements.anyCommon(Covered)) {
      Extensions.push_back(VP);
      Covered |= Elements;
    }
  };

  for (auto *OP : Frt.getUnresolvedPacks()) {
    OP = dedup(VPCtx, OP);
    const OperandProducerInfo &OPI = Pkr->getProducerInfo(VPCtx, OP);
    if (!OPI.Feasible)
      continue;
    for (auto *VP : OPI.Producers)
      Consider(VP);
  }

  BitVector CandidateMembers = CandidateSet->Members;
  CandidateMembers &= Frt.usableInstIds();
  for (auto *VP : CandidateSet->Packs)
    Consider(VP);
  return Extensions;
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
    std::stable_sort(
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
      bool Close = A.align(&I, &J) < 0;
      if (Close) {
        errs() << "ALIGNED " << I << ", " << J << ", COST = " << A.align(&I, &J)
               << '\n';
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
    // if (UseMCTS) {
    enumerateImpl(Enumerated, &I, VPCtx, AG, 64 /*beam width*/, 2 /*VL*/);
    enumerateImpl(Enumerated, &I, VPCtx, AG, 64 /*beam width*/, 4 /*VL*/);
    enumerateImpl(Enumerated, &I, VPCtx, AG, 64 /*beam width*/, 8 /*VL*/);
    enumerateImpl(Enumerated, &I, VPCtx, AG, 64 /*beam width*/, 16 /*VL*/);
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
    OP->OPIValid = false;
    auto &OPI = Pkr->getProducerInfo(VPCtx, OP);
    for (auto *VP : OPI.Producers)
      Packs.push_back(VP);
  }

  for (auto &I : *BB) {
    if (auto *LI = dyn_cast<LoadInst>(&I)) {
      for (unsigned VL : {2, 4, 8, 16 /*, 32, 64*/})
        for (auto *VP : getSeedMemPacks(Pkr, BB, LI, VL))
          Packs.push_back(VP);
    }
  }
  // for (auto &I : *BB) {
  //  if (auto *LI = dyn_cast<StoreInst>(&I)) {
  //    for (unsigned VL : {2, 4, 8, 16, 32, 64})
  //      for (auto *VP : getSeedMemPacks(Pkr, BB, LI, VL))
  //        Packs.push_back(VP);
  //  }
  //}
  return Packs;
}

struct State;
struct Transition {
  const State *Src = nullptr;
  const State *Dst = nullptr;
  Instruction *I = nullptr;
  const VectorPack *VP = nullptr;

  Transition(const State *Src, Instruction *I) : Src(Src), I(I) {}
  Transition(const State *Src, const VectorPack *VP) : Src(Src), VP(VP) {}
};

struct State {
  const Transition *Incoming = nullptr;
  Frontier Frt;
  std::vector<Transition> Transitions;
  float Cost = 0; // Cost so far
  float Est = 0;  // estimate of the cost from now on

  bool expanded() const { return !Transitions.empty() || isTerminal(); }
  bool isTerminal() const { return Frt.getFreeInsts().count() == 0; }
  void expand(const CandidatePackSet *);

  State(const Frontier &Frt) : Incoming(nullptr), Frt(Frt), Cost(0), Est(0) {}
  State(const State &) = default;
  State &operator=(const State &) = default;
};

// Fill out the children node
void State::expand(const CandidatePackSet *CandidateSet) {
  NamedRegionTimer Timer("expand-state", "expand search state",
                         "pack selection", "", UseTimer);

  assert(Transitions.empty() && "expanded already");
  auto *BB = Frt.getBasicBlock();

  BitVector UnusableIds = Frt.usableInstIds();
  UnusableIds.flip();
  bool CanExpandWithStore = false;

  for (auto *V : Frt.usableInsts()) {
    // Consider seed packs
    if (auto *SI = dyn_cast<StoreInst>(V)) {
      // for (unsigned VL : {2, 4, 8, 16, 32, 64}) {
      for (unsigned VL : {2, 4, 8, 16}) {
        if (auto *VP = getSeedStorePack(Frt, SI, VL)) {
          if (VP->getElements().anyCommon(UnusableIds))
            continue;
          CanExpandWithStore = true;
          Transitions.emplace_back(this, VP);
        }
      }

      if (CanExpandWithStore) {
        Transitions.emplace_back(this, SI);
        break;
      }
    }
  }

  if (CanExpandWithStore)
    return;

  auto Extensions = findExtensionPacks(Frt, CandidateSet);
  // Also consider the extension packs
  for (auto *VP : Extensions)
    Transitions.emplace_back(this, VP);

  if (Transitions.empty()) {
    for (auto *V : Frt.usableInsts()) {
      auto *I = dyn_cast<Instruction>(V);
      if (!I)
        continue;

      // Consider scalars
      Transitions.emplace_back(this, I);
      break;
    }
  }
}

float beamSearch(const Frontier *Frt, VectorPackSet &Packs,
                 const CandidatePackSet *CandidateSet,
                 unsigned BeamWidth = 500) {
  NamedRegionTimer Timer("beam-search", "beam search main loop",
                         "pack selection", "", UseTimer);

  auto *Pkr = Frt->getPacker();
  auto *TTI = Pkr->getTTI();

  Heuristic H(Pkr, Frt->getContext(), CandidateSet);

  std::vector<std::unique_ptr<State>> States;
  auto GetNext = [&](State *S, Transition *T) -> State * {
    NamedRegionTimer Timer("next-state", "creating the next state",
                           "pack selection", "", UseTimer);
    States.push_back(std::make_unique<State>(S->Frt));
    auto S2 = States.back().get();
    S2->Incoming = T;
    T->Dst = S2;
    float Cost;
    if (T->I)
      Cost = S2->Frt.advanceInplace(T->I, TTI);
    else
      Cost = S2->Frt.advanceInplace(T->VP, TTI);
    S2->Cost = S->Cost + Cost;
    S2->Est = H.getCost(&S2->Frt);
    return S2;
  };

  State *Best = nullptr;

  State Start(*Frt);
  std::vector<State *> Beam{&Start};
  std::vector<State *> NextBeam;
  while (!Beam.empty()) {
    NextBeam.clear();
    for (auto *S : Beam) {
      // if (!S->expanded())
      S->expand(CandidateSet);
      for (auto &T : S->Transitions) {
        auto *S2 = GetNext(S, &T);
        if (S2->isTerminal()) {
          if (!Best || Best->Cost > S2->Cost) {
            errs() << "new best cost: " << S2->Cost;
            Best = S2;
          }
        } else {
          NextBeam.push_back(S2);
        }
      }
    }
    Beam.swap(NextBeam);
    errs() << "BEAM SIZE = " << Beam.size() << '\n';

    std::stable_sort(Beam.begin(), Beam.end(),
                     [](const State *S, const State *S2) {
                       return S->Cost + S->Est < S2->Cost + S2->Est;
                     });
    if (Beam.size() > BeamWidth)
      Beam.resize(BeamWidth);
  }

  assert(Best);
  float BestCost = Best->Cost;
  const auto *S = Best;
  while (S->Incoming) {
    if (auto *VP = S->Incoming->VP) {
      errs() << "GOING WITH " << *VP << '\n';
      Packs.tryAdd(VP);
    }
    S = S->Incoming->Src;
  }
  return BestCost;
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

  return beamSearch(&Frt, Packs, &CandidateSet, 128);
}
