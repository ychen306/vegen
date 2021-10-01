#include "VectorPackContext.h"
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

  std::map<GeneralPackKey, std::unique_ptr<VectorPack>> GeneralPacks;
  std::map<std::pair<LoadPackKey, bool>, std::unique_ptr<VectorPack>> LoadPacks;
  std::map<std::pair<StorePackKey, bool>, std::unique_ptr<VectorPack>>
      StorePacks;
  std::map<PHIPackKey, std::unique_ptr<VectorPack>> PHIPacks;
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

VectorPack *VectorPackContext::createLoadPack(ArrayRef<LoadInst *> Loads,
                                              BitVector Elements,
                                              BitVector Depended,
                                              TargetTransformInfo *TTI,
                                              bool IsGather) const {
  VectorPackCache::LoadPackKey Key(Loads.begin(), Loads.end());
  auto &VP = PackCache->LoadPacks[{Key, IsGather}];
  if (VP)
    return VP.get();
  VP.reset(new VectorPack(this, IsGather, Loads, Elements, Depended, TTI));
  return VP.get();
}

VectorPack *VectorPackContext::createStorePack(ArrayRef<StoreInst *> Stores,
                                               BitVector Elements,
                                               BitVector Depended,
                                               TargetTransformInfo *TTI,
                                               bool IsScatter) const {
  VectorPackCache::StorePackKey Key(Stores.begin(), Stores.end());
  auto &VP = PackCache->StorePacks[{Key, IsScatter}];
  if (VP)
    return VP.get();
  VP.reset(new VectorPack(this, IsScatter, Stores, Elements, Depended, TTI));
  return VP.get();
}

VectorPack *VectorPackContext::createPhiPack(ArrayRef<PHINode *> PHIs,
                                             TargetTransformInfo *TTI) const {
  BitVector Elements(getNumValues());
  for (auto *PHI : PHIs)
    Elements.set(getScalarId(PHI));
  VectorPackCache::PHIPackKey Key(PHIs.begin(), PHIs.end());
  auto &VP = PackCache->PHIPacks[Key];
  if (VP)
    return VP.get();
  VP.reset(
      new VectorPack(this, PHIs, Elements, BitVector(getNumValues()), TTI));
  return VP.get();
}

VectorPack *VectorPackContext::createReduction(const ReductionInfo &Rdx,
                                               TargetTransformInfo *TTI) const {
  auto *Root = Rdx.Ops.front();
  auto &VP = PackCache->ReductionPacks[Root];
  if (!VP) {
    BitVector Elements(getNumValues());
    BitVector Depended(getNumValues());
    Elements.set(getScalarId(Root));
    VP.reset(new VectorPack(this, Rdx, Elements, Depended, TTI));
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
