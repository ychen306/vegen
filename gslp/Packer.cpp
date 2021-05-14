#include "Packer.h"
#include "MatchManager.h"

using namespace llvm;

namespace {

bool isScalarType(Type *Ty) { return Ty->getScalarType() == Ty; }

// Do a quadratic search to build the access dags
template <typename MemAccessTy>
void buildAccessDAG(ConsecutiveAccessDAG &DAG, ArrayRef<MemAccessTy *> Accesses,
                    const DataLayout *DL, ScalarEvolution *SE) {
  using namespace llvm;
  for (auto *A1 : Accesses) {
    // Get type of the value being acccessed
    auto *Ty =
        cast<PointerType>(A1->getPointerOperand()->getType())->getElementType();
    if (!isScalarType(Ty))
      continue;
    for (auto *A2 : Accesses) {
      if (A1->getType() == A2->getType() &&
          isConsecutiveAccess(A1, A2, *DL, *SE))
        DAG[A1].insert(A2);
    }
  }
}

} // end anonymous namespace

Packer::Packer(ArrayRef<InstBinding *> SupportedInsts, Function &F,
               AliasAnalysis *AA, const DataLayout *DL, ScalarEvolution *SE,
               TargetTransformInfo *TTI, BlockFrequencyInfo *BFI)
    : F(&F), SupportedInsts(SupportedInsts.vec()), TTI(TTI), BFI(BFI) {
  // Setup analyses and determine search space
  for (auto &BB : F) {
    std::vector<LoadInst *> Loads;
    std::vector<StoreInst *> Stores;
    // Find packable instructions
    auto MM = std::make_unique<MatchManager>(SupportedInsts, BB);
    for (auto &I : BB) {
      if (auto *LI = dyn_cast<LoadInst>(&I)) {
        if (LI->isSimple())
          Loads.push_back(LI);
      } else if (auto *SI = dyn_cast<StoreInst>(&I)) {
        if (SI->isSimple())
          Stores.push_back(SI);
      }
    }

    auto VPCtx = std::make_unique<VectorPackContext>(&BB);
    auto LoadDAG = std::make_unique<ConsecutiveAccessDAG>();
    auto StoreDAG = std::make_unique<ConsecutiveAccessDAG>();
    buildAccessDAG<LoadInst>(*LoadDAG, Loads, DL, SE);
    buildAccessDAG<StoreInst>(*StoreDAG, Stores, DL, SE);

    LoadInfo[&BB] = std::make_unique<AccessLayoutInfo>(*LoadDAG);
    StoreInfo[&BB] = std::make_unique<AccessLayoutInfo>(*StoreDAG);

    MMs[&BB] = std::move(MM);
    LDAs[&BB] = std::make_unique<LocalDependenceAnalysis>(AA, &BB, VPCtx.get());
    VPCtxs[&BB] = std::move(VPCtx);
    LoadDAGs[&BB] = std::move(LoadDAG);
    StoreDAGs[&BB] = std::move(StoreDAG);
  }
}

AccessLayoutInfo::AccessLayoutInfo(const ConsecutiveAccessDAG &AccessDAG) {
  // First pass to find leaders
  DenseSet<Instruction *> Followers;
  for (auto &AccessAndNext : AccessDAG) {
    Instruction *I = AccessAndNext.first;
    for (auto *Next : AccessAndNext.second)
      Followers.insert(Next);
  }

  for (auto &AccessAndNext : AccessDAG) {
    Instruction *Leader = AccessAndNext.first;
    if (Followers.count(Leader))
      continue;
    Info[Leader] = {Leader, 0};
    unsigned Offset = 0;
    auto *Followers = &AccessAndNext.second;
    for (;;) {
      for (auto *Follower : *Followers) {
        Info[Follower] = {Leader, Offset + 1};
      }
      if (Followers->empty())
        break;
      Instruction *Follower = *Followers->begin();
      auto It = AccessDAG.find(Follower);
      if (It == AccessDAG.end())
        break;
      Followers = &It->second;
      Offset += 1;
    }
    MemberCounts[Leader] = Offset;
  }
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
VectorPack *tryCoalesceLoads(const VectorPack *MainPack,
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

// TODO: do this properly
static void decomposeIntoLoadPacks(const SlotSet &Slots,
                                   VectorPackContext *VPCtx,
                                   LocalDependenceAnalysis &LDA,
                                   TargetTransformInfo *TTI,
                                   SmallVectorImpl<VectorPack *> &Extensions) {
#if 1
  for (unsigned VL : {2, 4, 8, 16, 32}) {
    for (unsigned i = Slots.minId(), e = Slots.maxId(); i <= e; i++) {
      BitVector Elements(VPCtx->getNumValues());
      BitVector Depended(VPCtx->getNumValues());
      std::vector<LoadInst *> Loads;
      for (unsigned j = i; j <= std::min(e, i+VL); j++) {
        auto *LI = Slots[i];
        if (LI) {
          Loads.push_back(cast<LoadInst>(LI));
          Elements.set(VPCtx->getScalarId(LI));
          Depended |= LDA.getDepended(LI);
        }
      }
      if (Elements.count())
        Extensions.push_back(VPCtx->createLoadPack(Loads, Elements, Depended, TTI));
    }
  }
#else
  BitVector Elements(VPCtx->getNumValues());
  BitVector Depended(VPCtx->getNumValues());
  std::vector<LoadInst *> Loads;
  for (unsigned i = Slots.minId(), e = Slots.maxId(); i <= e; i++) {
    auto *LI = Slots[i];
    if (LI) {
      Loads.push_back(cast<LoadInst>(LI));
      Elements.set(VPCtx->getScalarId(LI));
      Depended |= LDA.getDepended(LI);
    } else if (!Loads.empty()) {
      unsigned N = PowerOf2Ceil(Loads.size());
      while (Loads.size() != N)
        Loads.push_back(nullptr);
      Extensions.push_back(
          VPCtx->createLoadPack(Loads, Elements, Depended, TTI));
      Elements.reset();
      Depended.reset();
      Loads.clear();
    }
  }
  if (!Loads.empty()) {
    unsigned N = PowerOf2Ceil(Loads.size());
    while (Loads.size() != N)
      Loads.push_back(nullptr);
    Extensions.push_back(VPCtx->createLoadPack(Loads, Elements, Depended, TTI));
  }
#endif
}

// Assuming all elements of `OP` are loads, try to find an extending load pack.
void findExtendingLoadPacks(const OperandPack &OP, BasicBlock *BB, Packer *Pkr,
                            SmallVectorImpl<VectorPack *> &Extensions) {
#if 0
  auto &LayoutInfo = Pkr->getLoadInfo(BB);
  // mapping <leader> -> <slot set>
  DenseMap<Instruction *, SlotSet> Slots;
  for (auto *V : OP) {
    if (!V)
      continue;
    auto *LI = dyn_cast<LoadInst>(V);
    if (!LI)
      continue;
    auto &Info = LayoutInfo.get(LI);
    Slots[Info.Leader].try_insert(Info.Id, LI);
  }
  auto *VPCtx = Pkr->getContext(BB);
  auto &LDA = Pkr->getLDA(BB);
  auto *TTI = Pkr->getTTI();
  for (auto &LeaderAndSlots : Slots)
    decomposeIntoLoadPacks(LeaderAndSlots.second, VPCtx, LDA, TTI, Extensions);
#else
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
      Extensions.push_back(
          VPCtx->createLoadPack(Loads, Elements, Depended, Pkr->getTTI()));
      return;
    }
  }
#endif
}

const OperandProducerInfo &
Packer::getProducerInfo(const VectorPackContext *VPCtx, const OperandPack *OP) {
  if (OP->OPIValid)
    return OP->OPI;
  OP->OPIValid = true;
  auto &OPI = OP->OPI;
  OPI.Producers.clear();
  OPI.LoadProducers.clear();

  auto *BB = VPCtx->getBasicBlock();
  auto &LDA = *LDAs[BB];
  auto &MM = *MMs[BB];

  unsigned NumLanes = OP->size();
  BitVector Elements(VPCtx->getNumValues());
  BitVector Depended(VPCtx->getNumValues());
  OPI.Feasible = true;
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

    if (!I || I->getParent() != BB) {
      OPI.Feasible = false;
      continue;
    }

    unsigned InstId = VPCtx->getScalarId(I);
    if (!checkIndependence(LDA, *VPCtx, I, Elements, Depended))
      OPI.Feasible = false;
    Elements.set(InstId);
    Depended |= LDA.getDepended(I);
  }

  OPI.Elements = std::move(Elements);

  if (!OPI.Feasible)
    return OPI;

  if (AllLoads) {
    findExtendingLoadPacks(*OP, BB, this, OPI.LoadProducers);
    if (OPI.LoadProducers.empty())
      OPI.Feasible = false;
    return OPI;
  }

  if (HasUndef) {
    OPI.Feasible = false;
    return OPI;
  }

  for (auto *Inst : getInsts()) {
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
      OPI.Producers.push_back(
          VPCtx->createVectorPack(Lanes, OPI.Elements, Depended, Inst, TTI));
    }
  }
  OPI.Feasible = !OPI.Producers.empty();
  return OPI;
}

float Packer::getScalarCost(Instruction *I) {
  if (auto *LI = dyn_cast<LoadInst>(I)) {
    return TTI->getMemoryOpCost(Instruction::Load, LI->getType(),
        MaybeAlign(LI->getAlignment()), 0, LI);
  } 
  if (auto *SI = dyn_cast<StoreInst>(I))
    return TTI->getMemoryOpCost(Instruction::Store,
        SI->getValueOperand()->getType(),
        MaybeAlign(SI->getAlignment()), 0, SI);
  if (isa<GetElementPtrInst>(I))
    return 0;
  if (isa<PHINode>(I) ||
      isa<CallInst>(I) || isa<ReturnInst>(I) || I->isTerminator() ||
      isa<AllocaInst>(I))
    return 1;
  //return TTI->getInstructionCost(I, TargetTransformInfo::TCK_RecipThroughput);
  SmallVector<const Value *, 4> Operands(I->operand_values());
  return TTI->getArithmeticInstrCost(
      I->getOpcode(), I->getType(), TargetTransformInfo::OK_AnyValue,
      TargetTransformInfo::OK_AnyValue, TargetTransformInfo::OP_None,
      TargetTransformInfo::OP_None, Operands, I);
}
