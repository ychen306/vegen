#include "VectorPackContext.h"
#include "VectorPack.h"

using namespace llvm;

std::unique_ptr<VectorPack>
VectorPackContext::createVectorPack(std::vector<const Operation::Match *> Matches,
                                    BitVector Elements, BitVector Depended,
                                    const InstBinding *Producer) const {
  return std::unique_ptr<VectorPack>(new VectorPack(this, Matches, Elements, Depended, Producer));
}

std::unique_ptr<VectorPack> VectorPackContext::createLoadPack(ArrayRef<LoadInst *> Loads,
                                             BitVector Elements,
                                             BitVector Depended) const {
  return std::unique_ptr<VectorPack>(new VectorPack(this, Loads, Elements, Depended));
}

std::unique_ptr<VectorPack> VectorPackContext::createStorePack(ArrayRef<StoreInst *> Stores,
                                              BitVector Elements,
                                              BitVector Depended) const {
  return std::unique_ptr<VectorPack>(new VectorPack(this, Stores, Elements, Depended));
}

std::unique_ptr<VectorPack> VectorPackContext::createPhiPack(ArrayRef<PHINode *> PHIs) const {
  BitVector Elements(getNumValues());
  for (auto *PHI : PHIs)
    Elements.set(getScalarId(PHI));
  return std::unique_ptr<VectorPack>(new VectorPack(this, PHIs, Elements, BitVector(getNumValues())));
}
