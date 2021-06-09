#include "VectorPackContext.h"
#include "VectorPack.h"

using namespace llvm;

struct VectorPackCache {
  using GeneralPackKey =
      std::pair<decltype(VectorPack::Matches), const InstBinding *>;
  using LoadPackKey = decltype(VectorPack::Loads);
  using StorePackKey = decltype(VectorPack::Stores);
  using PHIPackKey = decltype(VectorPack::PHIs);

  std::map<GeneralPackKey, std::unique_ptr<VectorPack>> GeneralPacks;
  std::map<LoadPackKey, std::unique_ptr<VectorPack>> LoadPacks;
  std::map<StorePackKey, std::unique_ptr<VectorPack>> StorePacks;
  std::map<PHIPackKey, std::unique_ptr<VectorPack>> PHIPacks;
};

VectorPackContext::~VectorPackContext() = default;

VectorPackContext::VectorPackContext(BasicBlock *BB)
    : BB(BB), PackCache(std::make_unique<VectorPackCache>()) {
  unsigned i = 0;
  for (auto &I : *BB) {
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
                                              TargetTransformInfo *TTI) const {
  VectorPackCache::LoadPackKey Key(Loads.begin(), Loads.end());
  auto &VP = PackCache->LoadPacks[Key];
  if (VP)
    return VP.get();
  VP.reset(new VectorPack(this, Loads, Elements, Depended, TTI));
  return VP.get();
}

VectorPack *VectorPackContext::createStorePack(ArrayRef<StoreInst *> Stores,
                                               BitVector Elements,
                                               BitVector Depended,
                                               TargetTransformInfo *TTI) const {
  VectorPackCache::StorePackKey Key(Stores.begin(), Stores.end());
  auto &VP = PackCache->StorePacks[Key];
  if (VP)
    return VP.get();
  VP.reset(new VectorPack(this, Stores, Elements, Depended, TTI));
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
