#include "VectorPackContext.h"
#include "ControlDependence.h"
#include "Reduction.h"
#include "VectorPack.h"
#include "llvm/IR/InstIterator.h"

using namespace llvm;

struct VectorPackCache {
  using GeneralPackKey =
      std::pair<decltype(VectorPack::Matches), const InstBinding *>;
  using LoadPackKey = decltype(VectorPack::Loads);
  using StorePackKey = decltype(VectorPack::Stores);
  using PHIPackKey = decltype(VectorPack::PHIs);
  using GEPPackKey = decltype(VectorPack::GEPs);
  using GammaPackKey = decltype(VectorPack::Gammas);
  using CmpPackKey = decltype(VectorPack::Cmps);

  std::map<GeneralPackKey, std::unique_ptr<VectorPack>> GeneralPacks;
  std::map<std::pair<LoadPackKey, bool>, std::unique_ptr<VectorPack>> LoadPacks;
  std::map<std::pair<StorePackKey, bool>, std::unique_ptr<VectorPack>>
      StorePacks;
  std::map<PHIPackKey, std::unique_ptr<VectorPack>> PHIPacks;
  std::map<GammaPackKey, std::unique_ptr<VectorPack>> GammaPacks;
  std::map<GEPPackKey, std::unique_ptr<VectorPack>> GEPPacks;
  std::map<CmpPackKey, std::unique_ptr<VectorPack>> CmpPacks;
  std::map<Instruction *, std::unique_ptr<VectorPack>> ReductionPacks;
};

VectorPackContext::~VectorPackContext() = default;

VectorPackContext::VectorPackContext(Function *F)
    : F(F), PackCache(std::make_unique<VectorPackCache>()) {
  unsigned i = 0;
  for (Instruction &I : instructions(F)) {
    ScalarToIdMap[&I] = i++;
    Scalars.push_back(&I);
  }
}

VectorPack *VectorPackContext::createVectorPack(
    std::vector<const Operation::Match *> Matches, BitVector Elements,
    BitVector Depended, const InstBinding *Producer,
    TargetTransformInfo *TTI) const {
  VectorPackCache::GeneralPackKey Key{
      decltype(VectorPack::Matches)(Matches.begin(), Matches.end()), Producer};
  auto &VP = PackCache->GeneralPacks[Key];
  if (VP)
    return VP.get();
  VP.reset(new VectorPack(this, Matches, Elements, Depended, Producer, TTI));
  return VP.get();
}

VectorPack *VectorPackContext::createLoadPack(
    ArrayRef<LoadInst *> Loads, const ConditionPack *CP, BitVector Elements,
    BitVector Depended, TargetTransformInfo *TTI, bool IsGather) const {
  VectorPackCache::LoadPackKey Key(Loads.begin(), Loads.end());
  auto &VP = PackCache->LoadPacks[{Key, IsGather}];
  if (VP)
    return VP.get();
  VP.reset(new VectorPack(this, IsGather, CP, Loads, Elements, Depended, TTI));
  return VP.get();
}

VectorPack *VectorPackContext::createStorePack(
    ArrayRef<StoreInst *> Stores, const ConditionPack *CP, BitVector Elements,
    BitVector Depended, TargetTransformInfo *TTI, bool IsScatter) const {
  VectorPackCache::StorePackKey Key(Stores.begin(), Stores.end());
  auto &VP = PackCache->StorePacks[{Key, IsScatter}];
  if (VP)
    return VP.get();
  VP.reset(new VectorPack(this, IsScatter, CP, Stores, Elements, Depended, TTI));
  return VP.get();
}

VectorPack *VectorPackContext::createCmpPack(ArrayRef<CmpInst *> Cmps,
                                             BitVector Elements,
                                             BitVector Depended,
                                             TargetTransformInfo *TTI) const {
  VectorPackCache::CmpPackKey Key(Cmps.begin(), Cmps.end());
  auto &VP = PackCache->CmpPacks[Key];
  if (VP)
    return VP.get();
  VP.reset(new VectorPack(this, Cmps, Elements, Depended, TTI));
  return VP.get();
}

VectorPack *VectorPackContext::createPhiPack(ArrayRef<PHINode *> PHIs,
                                             TargetTransformInfo *TTI) const {
  BitVector Elements(getNumValues());
  for (auto *PHI : PHIs)
    Elements.set(getScalarId(PHI));
  VectorPackCache::PHIPackKey Key(PHIs.begin(), PHIs.end());
  auto &VP = PackCache->PHIPacks[Key];
  if (!VP) {
    VP.reset(
        new VectorPack(this, PHIs, Elements, BitVector(getNumValues()), TTI));
  }
  return VP.get();
}

VectorPack *
VectorPackContext::createGammaPack(ArrayRef<const GammaNode *> Gammas,
                                   TargetTransformInfo *TTI) const {
  BitVector Elements(getNumValues());
  for (auto *G : Gammas)
    Elements.set(getScalarId(G->PN));
  VectorPackCache::GammaPackKey Key(Gammas.begin(), Gammas.end());
  auto &VP = PackCache->GammaPacks[Key];
  if (!VP) {
    VP.reset(
        new VectorPack(this, Gammas, Elements, BitVector(getNumValues()), TTI));
  }
  return VP.get();
}

VectorPack *VectorPackContext::createGEPPack(ArrayRef<GetElementPtrInst *> GEPs,
                                             BitVector Elements,
                                             BitVector Depended,
                                             TargetTransformInfo *TTI) const {
  VectorPackCache::GEPPackKey Key(GEPs.begin(), GEPs.end());
  auto &VP = PackCache->GEPPacks[Key];
  if (!VP)
    VP.reset(new VectorPack(this, GEPs, Elements, Depended, TTI));
  return VP.get();
}

VectorPack *VectorPackContext::createReduction(const ReductionInfo &Rdx,
                                               unsigned RdxLen,
                                               TargetTransformInfo *TTI) const {
  auto *Root = Rdx.Ops.front();
  auto &VP = PackCache->ReductionPacks[Root];
  if (!VP) {
    BitVector Elements(getNumValues());
    BitVector Depended(getNumValues());
    Elements.set(getScalarId(Root));
    VP.reset(new VectorPack(this, Rdx, RdxLen, Elements, Depended, TTI));
  }
  return VP.get();
}

const OperandPack *VectorPackContext::dedup(const OperandPack *OP) const {
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
  return getCanonicalOperandPack(Deduped);
}

const OperandPack *VectorPackContext::even(const OperandPack *OP) const {
  OperandPack Even;
  unsigned i = 0;
  for (auto *V : *OP)
    if (i++ % 2)
      Even.push_back(V);
  return getCanonicalOperandPack(Even);
}

const OperandPack *VectorPackContext::odd(const OperandPack *OP) const {
  OperandPack Odd;
  unsigned i = 0;
  for (auto *V : *OP)
    if (i++ % 2 == 0)
      Odd.push_back(V);
  return getCanonicalOperandPack(Odd);
}

OperandPack *VectorPackContext::getCanonicalOperandPack(OperandPack OP) const {
  // Look for equivalent values in OP,
  // and replace them with a single, arbitrary value.
  for (unsigned i = 0; i < OP.size(); i++)
    for (unsigned j = i + 1; j < OP.size(); j++)
      if (EquivalentValues.isEquivalent(OP[i], OP[j]))
        OP[j] = OP[i];

  auto It = OperandCache.find(OP);
  if (It != OperandCache.end())
    return It->second.get();
  auto NewOP = std::make_unique<OperandPack>(OP);
  return (OperandCache[*NewOP] = std::move(NewOP)).get();
}

ConditionPack *VectorPackContext::getConditionPack(
    ArrayRef<const ControlCondition *> Conds,
    Optional<const ControlCondition *> MaybeCommon) const {
  const ControlCondition *CommonC =
      MaybeCommon ? *MaybeCommon : getGreatestCommonCondition(Conds);
  auto It = ConditionPackCache.find({Conds, CommonC});
  if (It != ConditionPackCache.end())
    return It->second.get();

  if (all_of(Conds, [CommonC](auto *C) { return C == CommonC; }))
    return nullptr;

  auto *NewCP = new ConditionPack;
  NewCP->Conds.assign(Conds.begin(), Conds.end());
  NewCP->ElemsToFlip.resize(Conds.size());
  ConditionPackCache[{NewCP->Conds, CommonC}].reset(NewCP);

  // See if there are duplicated conditions
  SmallPtrSet<const ControlCondition *, 8> Seen;
  for (auto *C : Conds)
    if (!Seen.insert(C).second) {
      NewCP->Kind = ConditionPack::CP_Infeasible;
      return NewCP;
    }

  if (all_of(Conds, [](auto *C) { return !C || isa<ConditionAnd>(C); })) {
    SmallVector<const ControlCondition *> Parents;
    OperandPack OP;
    for (auto Item : enumerate(Conds)) {
      auto *C = Item.value();
      unsigned i = Item.index();
      if (C) {
        auto *And = cast<ConditionAnd>(C);
        Parents.push_back(And->Parent);
        OP.push_back(And->Cond);
        if (!And->IsTrue)
          NewCP->ElemsToFlip.set(i);
      } else {
        Parents.push_back(nullptr);
        OP.push_back(nullptr);
      }
    }
    NewCP->Parent = getConditionPack(Parents, CommonC);
    NewCP->OP = getCanonicalOperandPack(OP);
    NewCP->Kind = ConditionPack::CP_And;
    return NewCP;
  }

  // Can't pack conditions that are mix of ANDs and ORs
  if (!all_of(Conds, [](auto *C) { return !C || isa<ConditionOr>(C); })) {
    NewCP->Kind = ConditionPack::CP_Infeasible;
    return NewCP;
  }

  unsigned MaxNumTerms = 0;
  for (auto *C : Conds) {
    if (!C)
      continue;
    auto *Or = cast<ConditionOr>(C);
    if (MaxNumTerms < Or->Conds.size())
      MaxNumTerms = Or->Conds.size();
  }

  for (unsigned i = 0; i < MaxNumTerms; i++) {
    SmallVector<const ControlCondition *> IthConds;
    for (auto *C : Conds) {
      auto *Or = dyn_cast_or_null<ConditionOr>(C);
      if (Or && i < Or->Conds.size())
        IthConds.push_back(Or->Conds[i]);
      else
        IthConds.push_back(nullptr);
    }
    NewCP->CPs.push_back(getConditionPack(IthConds, CommonC));
  }

  NewCP->Kind = ConditionPack::CP_Or;
  return NewCP;
}
