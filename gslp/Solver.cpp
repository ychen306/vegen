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
          UnresolvedScalars.set(InstId);
          Hash ^= VPCtx->getHashValue2(InstId);
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
  Hash ^= VPCtx->getHashValue(InstId);
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
  float Cost = 0;
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
    if (FreeInsts.test(InstId)) {
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
                            OpndPack)) {
      Hash ^= OpndPack->Hash;
      UnresolvedPacks.push_back(OpndPack);
    }
  }

  remove(UnresolvedPacks, ResolvedPackIds);
  std::sort(UnresolvedPacks.begin(), UnresolvedPacks.end());
  return Cost;
}

ShuffleTask::ShuffleTask(const BackwardShuffle *Shfl,
                         std::vector<const OperandPack *> Outputs,
                         const Frontier *Frt)
    : Shfl(Shfl), Outputs(Outputs),
      Inputs(Shfl->run(Frt->getContext(), Outputs)), Feasible(!Inputs.empty()) {
  if (!Feasible)
    return;
  auto UnresolvedPacks = Frt->getUnresolvedPacks();
  auto *Pkr = Frt->getPacker();
  auto *VPCtx = Frt->getContext();
  for (auto *OP : Inputs) {
    if (!Pkr->getProducerInfo(VPCtx, OP).Feasible ||
        std::binary_search(UnresolvedPacks.begin(), UnresolvedPacks.end(),
                           OP)) {
      Feasible = false;
      return;
    }
  }
}

float Frontier::advanceInplace(ShuffleTask ST, TargetTransformInfo *TTI) {
#if 1
  for (int i = (int)UnresolvedPacks.size() - 1; i >= 0; i--)
    for (auto *OP : ST.Outputs)
      if (UnresolvedPacks[i] == OP) {
        std::swap(UnresolvedPacks[i], UnresolvedPacks.back());
        UnresolvedPacks.pop_back();
        Hash ^= OP->Hash;
        break;
      }
#endif
  for (auto *OP : ST.Inputs)
    if (!std::binary_search(UnresolvedPacks.begin(), UnresolvedPacks.end(),
                            OP)) {
      UnresolvedPacks.push_back(OP);
      Hash ^= OP->Hash;
    }
  std::sort(UnresolvedPacks.begin(), UnresolvedPacks.end());
  return ST.getCost(TTI);
}

float Frontier::replaceAllUnresolvedPacks(ArrayRef<const OperandPack *> OPs,
                                          TargetTransformInfo *TTI) {
  float Cost = 0;
  for (auto *OP : OPs) {
    auto *VecTy = getVectorType(*OP);

    // Tick off instructions taking part in `OP`
    for (unsigned LaneId = 0; LaneId < OP->size(); LaneId++) {
      if (!(*OP)[LaneId])
        continue;
      auto *I = dyn_cast<Instruction>((*OP)[LaneId]);
      if (!I)
        continue;
      unsigned InstId = VPCtx->getScalarId(I);

      // Pay the extract cost
      if (UnresolvedScalars.test(InstId))
        Cost +=
            TTI->getVectorInstrCost(Instruction::ExtractElement, VecTy, LaneId);
    }
    const BitVector &Elements = Pkr->getProducerInfo(VPCtx, OP).Elements;

    for (auto *OP2 : UnresolvedPacks) {
      auto &OPI = Pkr->getProducerInfo(VPCtx, OP2);
      if (OPI.Elements.anyCommon(Elements))
        Cost += getGatherCost(*OP, *OP2, TTI);
    }
    Hash ^= OP->Hash;
  }

  for (auto *OP : UnresolvedPacks)
    Hash ^= OP->Hash;

  UnresolvedPacks.clear();
  UnresolvedPacks.insert(UnresolvedPacks.end(), OPs.begin(), OPs.end());
  std::sort(UnresolvedPacks.begin(), UnresolvedPacks.end());

  Shuffled = true;

  return 0;
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

raw_ostream &operator<<(raw_ostream &OS, const ShuffleTask &ST) {
  OS << "{\n";
  for (auto *OP : ST.Outputs)
    OS << *OP << '\n';
  OS << "} -> {\n";
  for (auto *OP : ST.Inputs)
    OS << *OP << '\n';
  OS << "}\n";
  return OS;
}

static std::vector<VectorPack *> findExtensionPacks(const Frontier &Frt);

raw_ostream &operator<<(raw_ostream &OS, const Frontier &Frt) {
  OS << "============== FRONTIER STATE ==========\n";
  OS << "UNRESOLVED VECTOR OPERANDS: <<<<<<<<<<<<<<<<<<<<<<\n";
  for (auto *OP : Frt.getUnresolvedPacks())
    OS << *OP << '\n';
  OS << ">>>>>>>>>>>>>>>\n";
  OS << "UNRESOLVED SCALAR OPERANDS: <<<<<<<<<<<<\n";
  for (auto *V : Frt.getUnresolvedScalars())
    OS << V->getName() << ", ";
  OS << ">>>>>>>>>>>>>>>\n";
  return OS;
}

std::unique_ptr<Frontier> Frontier::advance(const VectorPack *VP, float &Cost,
                                            llvm::TargetTransformInfo *TTI,
                                            bool Shuffled) const {
  auto Next = std::make_unique<Frontier>(*this);
  Cost = Next->advanceInplace(VP, TTI);
  std::sort(Next->UnresolvedPacks.begin(), Next->UnresolvedPacks.end());
  Next->Shuffled |= Shuffled;
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

UCTNode *UCTNodeFactory::getNode(const Frontier *Frt,
                                 const PartialShuffle *PS) {
  Nodes.push_back(std::unique_ptr<UCTNode>(new UCTNode(Frt, PS)));
  return Nodes.back().get();
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

extern VectorPack *tryCoalesceLoads(const VectorPack *MainPack,
                                    ArrayRef<VectorPack *> OtherPacks,
                                    Packer *Pkr);

std::vector<const OperandPack *> Enumerated;
BitVector EnumeratedIds;

static std::vector<VectorPack *> findExtensionPacks(const Frontier &Frt) {
  auto *Pkr = Frt.getPacker();
  auto *VPCtx = Frt.getContext();

  // Put load extensions in a separate category.
  // We don't extend with a load pack if we can extend with other arithmetic
  // packs
  std::vector<VectorPack *> LoadExtensions;

  BitVector UnusableIds = Frt.usableInstIds();
  UnusableIds.flip();

  std::vector<VectorPack *> Extensions;

#if 1
  BitVector X = EnumeratedIds;
  X &= Frt.usableInstIds();
  if (X.count()) {
    unsigned InstId = *X.set_bits_begin();
    for (auto *OP : Enumerated) {
      auto &OPI = Pkr->getProducerInfo(VPCtx, OP);
      if (!OPI.Elements.test(InstId) || OPI.Elements.anyCommon(UnusableIds))
        continue;
      for (auto *VP : OPI.Producers)
        Extensions.push_back(VP);
    }
  }
  if (!Extensions.empty())
    return Extensions;
#endif

  for (auto *OP : Frt.getUnresolvedPacks()) {
    //if (!Extensions.empty())
    //  return Extensions;
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
            LoadVP, ArrayRef<VectorPack *>(LoadExtensions).slice(1), Pkr)) {
      return {Coalesced, LoadVP};
    }
    return {LoadVP};
  }
  return {};
}

static std::vector<VectorPack *> getSeedStorePacks(const Frontier &Frt,
                                                   StoreInst *SI, unsigned VL) {
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

static VectorPack *getSeedStorePack(const Frontier &Frt, StoreInst *SI,
                                    unsigned VL) {
  auto Seeds = getSeedStorePacks(Frt, SI, VL);
  if (Seeds.empty())
    return nullptr;
  return Seeds[0];
}

// Hack! purely for debugging
struct : public BackwardShuffle {
  std::vector<const OperandPack *>
  run(const VectorPackContext *VPCtx,
      ArrayRef<const OperandPack *> Outputs) const override {
#if 1
    if (Outputs.size() != 1)
      return {};
    auto &OP = *Outputs[0];
    if (OP.size() != 64)
      return {};
    OperandPack Inputs[8];
    for (unsigned i = 0; i < 64; i++) {
      Inputs[i % 8].push_back(OP[i]);
    }
    std::vector<const OperandPack *> Canonicalized;
    for (auto &OP : Inputs) {
      Canonicalized.push_back(VPCtx->getCanonicalOperandPack(OP));
    }
    return Canonicalized;
#else
    if (Outputs.size() != 2)
      return {};

    const OperandPack &Lo = *Outputs[0];
    const OperandPack &Hi = *Outputs[1];
    if (Lo.size() != Hi.size())
      return {};

    OperandPack A, B;
    for (unsigned i = 0; i < Lo.size(); i++) {
      if (i % 2)
        A.push_back(Lo[i]);
      else
        B.push_back(Lo[i]);
    }
    for (unsigned i = 0; i < Hi.size(); i++) {
      if (i % 2)
        A.push_back(Hi[i]);
      else
        B.push_back(Hi[i]);
    }
    auto *OP1 = VPCtx->getCanonicalOperandPack(A);
    auto *OP2 = VPCtx->getCanonicalOperandPack(B);
    if (OP1 == OP2)
      return {OP1};
    return {OP1, OP2};
#endif
  }
  float getCost(llvm::TargetTransformInfo *) const override { return 1.0; }
} UnpackHiLo;

struct : public BackwardShuffle {
  std::vector<const OperandPack *>
  run(const VectorPackContext *VPCtx,
      ArrayRef<const OperandPack *> Outputs) const override {
    if (Outputs.size() != 2)
      return {};

    OperandPack OP = *Outputs[0];
    for (auto *V : *Outputs[1])
      OP.push_back(V);
    return {VPCtx->getCanonicalOperandPack(OP)};
  }
  float getCost(llvm::TargetTransformInfo *) const override { return 4.0; }
} Combine;

struct : public BackwardShuffle {
  std::vector<const OperandPack *>
  run(const VectorPackContext *VPCtx,
      ArrayRef<const OperandPack *> Outputs) const override {
    if (Outputs.size() != 1)
      return {};

    OperandPack A, B;
    OperandPack OP = *Outputs[0];
    unsigned N = OP.size();
    if (N < 2)
      return {};
    unsigned i = 0;
    for (; i < N / 2; i++)
      A.push_back(OP[i]);
    for (; i < N; i++)
      B.push_back(OP[i]);

    auto *OP1 = VPCtx->getCanonicalOperandPack(A);
    auto *OP2 = VPCtx->getCanonicalOperandPack(B);
    if (OP1 == OP2)
      return {OP1};
    return {OP1, OP2};
  }
  float getCost(llvm::TargetTransformInfo *) const override { return 2.0; }
} Split;

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

std::unique_ptr<Aligner> TheAligner;

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
void enumerateImpl(std::vector<const OperandPack *> &Enumerated,
    Instruction *I, VectorPackContext *VPCtx,
              const AlignmentGraph &AG, unsigned BeamWidth, unsigned VL) {
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

  for (unsigned i = 0; i < VL-1; i++) {
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
    Candidates.resize(BeamWidth);
  }

  for (auto &Cand : Candidates)
    if (Cand.OP.size() == VL) {
      Enumerated.push_back(VPCtx->getCanonicalOperandPack(Cand.OP));
    }
}

std::vector<const OperandPack *> enumerate(BasicBlock *BB, Packer *Pkr) {
  auto &LDA = Pkr->getLDA(BB);
  auto *VPCtx = Pkr->getContext(BB);
  Aligner A(BB, Pkr);

  AlignmentGraph AG;
  for (auto &I : *BB) {
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
      float AlignmentCost = A.align(&I, &J);
      if (AlignmentCost < 0) {
        errs() << "ALIGNED " << I << " AND " << J
               << ", COST = " << AlignmentCost << '\n';
        AG[&I].push_back({&J, AlignmentCost});
      }
    }
  }

  unsigned NumCands = 0;
  std::vector<const OperandPack *> Enumerated;
  for (auto &I : *BB) {
    if (!usedByStore(&I))
      continue;
    unsigned OldSize = Enumerated.size();
    enumerateImpl(Enumerated, &I, VPCtx, AG, 64/*beam width*/, 8/*VL*/);
    for (unsigned i = OldSize; i < Enumerated.size(); i++)
      errs() << "!!! candidate: " << *Enumerated[i] << '\n';
  }
  errs() << "!!! num candidates: " << Enumerated.size() << '\n';
  return Enumerated;;
}

PartialShuffle::PartialShuffle(const VectorPackContext *VPCtx,
                               unsigned MaxNumOperands) {
  for (unsigned i = 0; i < MaxNumOperands; i++)
    NewOperands.emplace_back(VPCtx->getNumValues());
  Scalarized = BitVector(VPCtx->getNumValues());
  Decided = BitVector(VPCtx->getNumValues());
}

PartialShuffle::PartialShuffle(const Frontier *Frt) {
  auto *VPCtx = Frt->getContext();
  auto *Pkr = Frt->getPacker();
  Scalarized = BitVector(VPCtx->getNumValues());
  Decided = BitVector(VPCtx->getNumValues());

  for (auto *OP : Frt->getUnresolvedPacks()) {
    auto &Elements = Pkr->getProducerInfo(VPCtx, OP).Elements;
    NewOperands.push_back(Elements);
    Decided |= Elements;
  }
  auto Undecided = getUndecided(*Frt);
  for (unsigned i : Undecided.set_bits()) {
    Scalarized.set(i);
    Decided.set(i);
  }
}

static OperandPack *buildOperandPack(const VectorPackContext *VPCtx,
                                     const BitVector &Elements) {
  OperandPack OP;
  for (unsigned i : Elements.set_bits())
    OP.push_back(VPCtx->getScalar(i));
  return VPCtx->getCanonicalOperandPack(OP);
}

void PartialShuffle::dump(const VectorPackContext *VPCtx) const {
  for (auto &Elems : NewOperands)
    if (Elems.count())
      errs() << *buildOperandPack(VPCtx, Elems) << '\n';
};

std::vector<const OperandPack *>
PartialShuffle::getOperandPacks(const VectorPackContext *VPCtx) const {
  std::vector<const OperandPack *> OperandPacks;
  for (auto &Elements : NewOperands)
    if (Elements.count())
      OperandPacks.push_back(buildOperandPack(VPCtx, Elements));
  return OperandPacks;
}

float PartialShuffle::sample(Frontier &Frt) const {
  BitVector Undecided = getUndecided(Frt);
  auto *Pkr = Frt.getPacker();
  auto *VPCtx = Frt.getContext();
  auto *TTI = Pkr->getTTI();

  auto SampledOperands = NewOperands;

  float Cost = 0;
  std::vector<std::vector<Instruction *>> OperandElems;
  for (auto &Elems : SampledOperands) {
    std::vector<Instruction *> ElemsVec;
    for (unsigned i : Elems.set_bits())
      ElemsVec.push_back(cast<Instruction>(VPCtx->getScalar(i)));
    OperandElems.push_back(ElemsVec);
  }

  std::vector<unsigned> UndecidedIds;
  for (unsigned i : Undecided.set_bits())
    UndecidedIds.push_back(i);
  std::random_shuffle(UndecidedIds.begin(), UndecidedIds.end(), rand_int);

  for (unsigned i : UndecidedIds) {
    auto *I = cast<Instruction>(VPCtx->getScalar(i));
    int BestOperand = -1;
    int BestAlignmentScore;
    for (unsigned j = 0; j < OperandElems.size(); j++) {
      unsigned N = OperandElems[j].size();
      if (N >= 16)
        continue;
      if (N == 0) {
        continue;
        if (rand_int(8) == 0) {
          BestOperand = j;
          break;
        }
        continue;
      }

      float Score = TheAligner->align(OperandElems[j][rand_int(N)], I);
      if (BestOperand == -1 || Score < BestAlignmentScore) {
        BestOperand = j;
        BestAlignmentScore = Score;
      }
    }
    if (BestOperand == -1)
      BestOperand = rand_int(OperandElems.size());
    OperandElems[BestOperand].push_back(I);
    SampledOperands[BestOperand].set(i);
  }
  // std::vector<unsigned> UndecidedIds;
  // for (unsigned i : Undecided.set_bits())
  //  UndecidedIds.push_back(i);
  // std::random_shuffle(UndecidedIds.begin(), UndecidedIds.end(), rand_int);
  // for (auto &Elems : SampledOperands) {
  //  unsigned Count = Elems.count();
  //  if (UndecidedIds.empty())
  //    break;
  //  while (Count++ < 16 && !UndecidedIds.empty()) {
  //    unsigned i = UndecidedIds.back();
  //    UndecidedIds.pop_back();
  //    Elems.set(i);
  //  }
  //}

#if 0
  for (unsigned i : Undecided.set_bits()) {
    //unsigned P = rand_int(NewOperands.size() + 1);
    unsigned P = rand_int(NewOperands.size() );
    //if (P == NewOperands.size())
    //  Cost += Frt.advanceInplace(cast<Instruction>(VPCtx->getScalar(i)), TTI);
    //else
      SampledOperands[P].set(i);
  }
#endif

  std::vector<const OperandPack *> OPs;
  for (auto &Elements : SampledOperands) {
    if (Elements.count() == 0)
      continue;
    auto *OP = buildOperandPack(VPCtx, Elements);
    OPs.push_back(OP);
    // auto *OP = buildOperandPack(VPCtx, Elements);
    // auto &OPI = Pkr->getProducerInfo(VPCtx, OP);
    // if (unsigned N = OPI.Producers.size()) {
    //  // Sample a random producer
    //  auto *VP = OPI.Producers[rand_int(N)];
    //  Cost += Frt.advanceInplace(VP, TTI);
    //} else {
    //  // just scalarize everything if this operand pack is not feasible
    //  for (unsigned i : Elements.set_bits())
    //    Cost += Frt.advanceInplace(cast<Instruction>(VPCtx->getScalar(i)),
    //    TTI);
    //}
  }
  for (unsigned i : Scalarized.set_bits())
    Cost += Frt.advanceInplace(cast<Instruction>(VPCtx->getScalar(i)), TTI);
  Cost = Frt.replaceAllUnresolvedPacks(OPs, TTI);
  return Cost;
}

// Fill out the children node
void UCTNode::expand() {
  assert(Transitions.empty() && "expanded already");
  auto *Pkr = getPacker();

  auto *BB = Frt->getBasicBlock();

  bool CanExpandWithStore = false;

  for (auto *V : Frt->usableInsts()) {
    // Consider seed packs
    if (auto *SI = dyn_cast<StoreInst>(V)) {
      for (unsigned VL : {2, 4, 8, 16, 32, 64}) {
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

  auto Extensions = findExtensionPacks(*Frt);
  // Also consider the extension packs
  for (auto *VP : Extensions)
    Transitions.emplace_back(VP, true /*disable shuffling*/);

  //BitVector UnusableIds = Frt->usableInstIds();
  //UnusableIds.flip();
  //auto *VPCtx = Frt->getContext();
  //for (auto *OP : Enumerated) {
  //  auto &OPI = Pkr->getProducerInfo(VPCtx, OP);
  //  if (OPI.Elements.anyCommon(UnusableIds))
  //    continue;
  //  for (auto *VP : OPI.Producers)
  //    Transitions.emplace_back(VP);
  //}

  if (Transitions.empty()) {
    for (auto *V : Frt->usableInsts()) {
      auto *I = dyn_cast<Instruction>(V);
      if (!I)
        continue;

      // Consider scalars
      Transitions.emplace_back(I);
    }
  }

#if 0
  // Only allow shuffle in the beginning
  if (Frt->shuffled())
    return;

  // Consider shuffles
  ArrayRef<const OperandPack *> UnresolvedPacks = Frt->getUnresolvedPacks();
  for (auto *OP1 : UnresolvedPacks) {
    ShuffleTask ST(&Split, {OP1}, Frt);
    if (ST.feasible()) {
      Transitions.emplace_back(std::move(ST));
    }
    for (auto *OP2 : UnresolvedPacks) {
      ShuffleTask ST(&UnpackHiLo, {OP1, OP2}, Frt);
      if (ST.feasible()) {
        Transitions.emplace_back(std::move(ST));
      }

      ST = ShuffleTask(&Combine, {OP1, OP2}, Frt);
      if (ST.feasible()) {
        Transitions.emplace_back(std::move(ST));
      }
    }
  }
#endif
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

    // Deal with cycle
    DenseSet<UCTNode *> Visited;

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
      bool FirstFeasible =
          !Visited.count(BestT->getNext(CurNode, Factory, TTI));
      float MaxUCTScore = 0;
      if (FirstFeasible && BestT->visited())
        MaxUCTScore = ScoreTransition(0);

      for (unsigned i = 0; i < Transitions.size(); i++) {
        auto &T = Transitions[i];
        if (Visited.count(T.getNext(CurNode, Factory, TTI)))
          continue;
        if (!T.visited()) {
          BestT = &T;
          break;
        }

        float UCTScore = ScoreTransition(i);
        if (!FirstFeasible || UCTScore > MaxUCTScore) {
          MaxUCTScore = UCTScore;
          BestT = &T;
        }
      }

      if (Visited.count(BestT->getNext(CurNode, Factory, TTI)))
        abort();
      Path.push_back(FullTransition{CurNode, BestT});
      CurNode = BestT->getNext(CurNode, Factory, TTI);
      Visited.insert(CurNode);
    }

    float LeafCost = 0;
    // ========= 2) Expansion ==========
    if (!CurNode->isTerminal()) {
      // ======= 3) Evaluation/Simulation =======
      LeafCost = evalLeafNode(CurNode);
      if (CurNode->visitCount() >= ExpandThreshold) {
        CurNode->expand();
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

float makeOperandPacksUsable(Frontier &Frt) {
  auto *Pkr = Frt.getPacker();
  auto *TTI = Pkr->getTTI();
  auto *BB = Frt.getBasicBlock();
  auto *VPCtx = Frt.getContext();

  float Cost = 0;

  BitVector VectorOperandSet(VPCtx->getNumValues());
  for (auto *OP : Frt.getUnresolvedPacks())
    VectorOperandSet |= Pkr->getProducerInfo(VPCtx, OP).Elements;

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
  if (auto *PS = N->getPartialShuffle()) {
    Frontier Frt = *N->getFrontier();
    PS->sample(Frt);
    float Cost = Evaluator->evaluate(&Frt);
    // errs() << "!! COST FROM SAMPLING = " << Cost << '\n';
    // errs() << "STATE AFTER SAMPLING:\n";
    // PS->dump(Frt.getContext());
    // errs() << Frt << '\n';
    // if (Cost < -1e3) {
    //  abort();
    //}
    return Cost;
  }
  return Evaluator->evaluate(N->getFrontier());
}

// Uniformly random rollout
float RolloutEvaluator::evaluate(const Frontier *Frt) {
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
  std::vector<VectorPack *> Extensions;
  do {
    Changed = false;
    Extensions = getExtensions(ScratchFrt);
    while (!Extensions.empty()) {
      auto *VP = Extensions[rand_int(Extensions.size())];
      Cost += ScratchFrt.advanceInplace(VP, TTI);
      Extensions = getExtensions(ScratchFrt);

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
}

float estimateCost(Frontier Frt, VectorPack *VP) {
  auto *Pkr = Frt.getPacker();
  auto *BB = Frt.getBasicBlock();
  auto &LDA = Pkr->getLDA(BB);
  auto *VPCtx = Pkr->getContext(BB);
  auto *TTI = Pkr->getTTI();

  float Cost = Frt.advanceInplace(VP, TTI);
  return Cost + RolloutEvaluator().evaluate(&Frt);
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

class DPSolver {
  struct Solution {
    float Cost;
    const VectorPack *VP;
    bool Fill;
    Optional<ShuffleTask> ST;

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
    auto Extensions = findExtensionPacks(Frt);
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

float optimizeBottomUp(VectorPackSet &Packs, Packer *Pkr, BasicBlock *BB) {
  Frontier Frt(BB, Pkr);
#if 0
  {
    auto ScratchFrt = Frt;
    auto *TTI = Pkr->getTTI();
    auto *VPCtx = Frt.getContext();
    for (auto &I : *BB) {
      if (isa<StoreInst>(&I))
        ScratchFrt.advanceInplace(&I, TTI);
    }
    for (auto *OP : enumerate(BB, Pkr)) {
      DPSolver Solver(TTI);
      auto Frt2 = ScratchFrt;

      auto &OPI = Pkr->getProducerInfo(VPCtx, OP);
      if (!OPI.Feasible) {
        errs() << *OP << " is infeasible\n";
        continue;
      }
      Frt2.advanceInplace(OPI.Producers[0], TTI);

      errs() << "!!!!!!!!1 simulating\n";
      auto Sol = Solver.solve(Frt2);
      errs() << "Cost of " << *OP << " is " << Sol.Cost << '\n';
      for (;;) {
        auto Sol = Solver.solve(Frt2);

        if (auto *ExtVP = Sol.VP) {
          Frt2.advanceInplace(ExtVP, TTI);
          errs() << "!!! [sim] adding : " << *ExtVP << '\n';
        } else if (Sol.Fill) {
          makeOperandPacksUsable(Frt2);
        } else {
          break;
        }
        // errs() << "!!! Adding : " << *ExtVP << '\n';
        // errs() << "\t updated cost: " << Cost << '\n';
      }


    }
    exit(1);
  }
#endif
  {
    Enumerated = enumerate(BB, Pkr);
    auto *VPCtx = Frt.getContext();
    EnumeratedIds = BitVector(VPCtx->getNumValues());
    for (auto *OP : Enumerated)  {
      EnumeratedIds |= Pkr->getProducerInfo(VPCtx, OP).Elements;
    }
  }

  auto &StoreDAG = Pkr->getStoreDAG(BB);
  TheAligner.reset(new Aligner(BB, Pkr));

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
  // std::vector<unsigned> VL{16, 8, 4, 2};
  // VL = {8};
  // VL = {4};
  // VL = {64};
  VL = {16};
  VL = { 64 };
  VL = {8};
  float Cost = 0;
  float BestEst = 0;

#if 1
  for (unsigned i : VL) {
    for (auto *SI : Stores) {
      auto *SeedVP = getSeedStorePack(Frt, SI, i);
      if (SeedVP) {
        Cost += Frt.advanceInplace(SeedVP, TTI);
        //auto *OP = Frt.getUnresolvedPacks()[0];
        //Cost += Frt.advanceInplace(ShuffleTask(&UnpackHiLo, {OP}, &Frt),
        //TTI);
        Packs.tryAdd(SeedVP);
        //ShuffleTask ST(&UnpackHiLo, {OP}, &Frt);
        //Enumerated.clear();
        //auto *VPCtx = Frt.getContext();
        //EnumeratedIds = BitVector(VPCtx->getNumValues());
        //for (auto *OP : ST.Inputs) {
        //  EnumeratedIds |= Pkr->getProducerInfo(VPCtx, OP).Elements;
        //  Enumerated.push_back(OP);
        //}
        continue;
#if 0
          float Est = estimateCost(Frt, SeedVP);
#else
        float LocalCost;
        errs() << "Estimating seed pack " << *SeedVP << '\n';
        auto Sol = Solver.solve(Frt.advance(SeedVP, LocalCost, TTI));
        float Est = LocalCost + Sol.Cost;
#endif
        errs() << "Estimated cost of " << *SeedVP << " is " << Est
               << ", local cost: " << LocalCost << ", trans cost: " << Sol.Cost
               << '\n';
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
            errs() << "????\n";
            auto Sol = Solver.solve(Frt);
            if (auto *ExtVP = Sol.VP) {
              errs() << "Adding pack " << *ExtVP << '\n';
              Cost += Frt.advanceInplace(ExtVP, TTI);
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
#endif
  Aligner TheAligner(BB, Pkr);

  if (false) {
    PartialShuffle PS(&Frt);
    float Cost = PS.sample(Frt);
    // errs() << "!! cost = " << Cost << '\n';
    // errs() << Frt << '\n';
    // abort();
  }

#if 1
  UCTNodeFactory Factory;
  RolloutEvaluator Evaluator;
  UCTSearch MCTS(0.01 /*c*/, 0.0 /*w*/, 0 /*ExpandThreshold*/, &Factory, Pkr,
                 nullptr /*Policy*/, &Evaluator, TTI);
  UCTNode *Root = Factory.getNode(std::make_unique<Frontier>(Frt));
  unsigned NumSimulations = 1000;
  float TotalCost = 0;
  Root->expand();
  DenseSet<UCTNode *> Visited;
  auto IsWorse = [](const UCTNode::Transition &A,
                    const UCTNode::Transition &B) -> bool {
    // return A.Count < B.Count;
    float ACost = -A.Cost - A.Next->minCost();
    float BCost = -B.Cost - B.Next->minCost();
    return std::tie(ACost, A.Count) < std::tie(BCost, B.Count);
  };

  while (!Root->isTerminal()) {
    MCTS.run(Root, NumSimulations);
    assert(Root->expanded());
    Visited.insert(Root);

    if (Root->transitions().empty())
      break;

    auto &Transitions = Root->transitions();
    errs() << "NUM TRANSITIONS : " << Transitions.size() << '\n';

#if 0
    UCTNode::Transition *T = &*std::max_element(
        Transitions.begin(), Transitions.end(),

        [](const UCTNode::Transition &A, const UCTNode::Transition &B) {
          float ACost = -A.Cost - A.Next->minCost();
          float BCost = -B.Cost - B.Next->minCost();
          return std::tie(ACost, A.Count) < std::tie(BCost, B.Count);
        });
#else
    UCTNode::Transition *T = nullptr;
    for (auto &T2 : Transitions) {
      if (Visited.count(T2.getNext(Root, &Factory, TTI)))
        continue;
      if (!T || IsWorse(*T, T2))
        T = &T2;
    }
    if (!T)
      abort();
#endif

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

    if (auto *PS = Node->getPartialShuffle()) {
      errs() << "NUM UNDECIDED "
             << PS->getUndecided(*Node->getFrontier()).count() << '\n';
    }

    if (T->VP) {
      errs() << "[MCTS] ADDING: " << *T->VP << '\n';
      Packs.tryAdd(T->VP);
    } else if (T->ST) {
      errs() << "[MCTS] Going with shuffle: " << T->ST << '\n';
    } else if (T->I) {
      errs() << "[MCTS] Scalarizing: " << *T->I << '\n';
    } else {
      errs() << "===========PARTIAL SHUFFLE STATE===========\n";
      T->PS->dump(Root->getFrontier()->getContext());
    }
    Root = T->getNext(Root, &Factory, TTI);
    TotalCost += T->transitionCost();
    errs() << "[MCTS] New cost: " << TotalCost << '\n';
    errs() << *Root->getFrontier() << '\n';
  }
#else
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
#endif

  return Cost;
}
