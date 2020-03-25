#include "VectorPackContext.h"
#include "VectorPack.h"

using namespace llvm;

VectorPack
VectorPackContext::createVectorPack(std::vector<Operation::Match> Matches,
                                    BitVector Elements, BitVector Depended,
                                    const InstBinding *Producer) const {
  return VectorPack(this, Matches, Elements, Depended, Producer);
}

VectorPack VectorPackContext::createLoadPack(ArrayRef<LoadInst *> Loads,
                                             BitVector Elements,
                                             BitVector Depended) const {
  return VectorPack(this, Loads, Elements, Depended);
}

VectorPack VectorPackContext::createStorePack(ArrayRef<StoreInst *> Stores,
                                              BitVector Elements,
                                              BitVector Depended) const {
  return VectorPack(this, Stores, Elements, Depended);
}

VectorPack VectorPackContext::createPhiPack(ArrayRef<PHINode *> PHIs) const {
  BitVector Elements(getNumValues());
  for (auto *PHI : PHIs)
    Elements.set(getScalarId(PHI));
  return VectorPack(this, PHIs, Elements, BitVector(getNumValues()));
}
