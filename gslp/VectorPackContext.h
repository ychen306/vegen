#ifndef VECTOR_PACK_CONTEXT_H
#define VECTOR_PACK_CONTEXT_H

#include "InstSema.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/BitVector.h"
#include <vector>

// VectorPackContext captures various meta data we use to create and manage
// vector packs. Basically we want to store vector packs are a bitvector, and we
// need this class to manage the mapping between a value and its integer id
class VectorPack;
class VectorPackContext {
  llvm::BasicBlock *BB;
  std::vector<llvm::Value *> Scalars;

public:
  VectorPackContext(llvm::BasicBlock *BB) : BB(BB) {
    for (auto &I : *BB)
      Scalars.push_back(&I);
    std::sort(Scalars.begin(), Scalars.end());
  }

  // Create a "General" vector pack
  VectorPack createVectorPack(std::vector<llvm::Optional<Operation::Match>> Matches,
                              llvm::BitVector Elements, llvm::BitVector Depended,
                              const InstBinding *Producer) const;

  // Create a vectorized load
  VectorPack createLoadPack(llvm::ArrayRef<llvm::LoadInst *> Loads, llvm::BitVector Elements,
                            llvm::BitVector Depended) const;

  // Create a vectorized store
  VectorPack createStorePack(llvm::ArrayRef<llvm::StoreInst *> Stores, llvm::BitVector Elements,
                             llvm::BitVector Depended) const;

  // Create a vectorized phi
  VectorPack createPhiPack(llvm::ArrayRef<llvm::PHINode *> PHIs) const;

  llvm::Value *getScalar(unsigned Id) const {
    assert(Id < Scalars.size());
    return Scalars[Id];
  }

  bool isKnownValue(const llvm::Value *V) const {
    auto It = std::lower_bound(Scalars.begin(), Scalars.end(), V);
    return It != Scalars.end() && Scalars[It - Scalars.begin()] == V;
  }

  unsigned getScalarId(const llvm::Value *V) const {
    auto It = std::lower_bound(Scalars.begin(), Scalars.end(), V);
    assert(llvm::cast<llvm::Instruction>(V)->getParent() == BB);
    assert(It != Scalars.end());
    assert(Scalars[It - Scalars.begin()] == V);
    return It - Scalars.begin();
  }

  unsigned getNumValues() const { return Scalars.size(); }
  llvm::BasicBlock *getBasicBlock() const { return BB; }

  // Fixme : templatize this to decouple use of bitvector
  class value_iterator {
    const VectorPackContext *VPCtx;
    llvm::BitVector::const_set_bits_iterator Handle;

  public:
    value_iterator(const VectorPackContext *VPCtx,
                   llvm::BitVector::const_set_bits_iterator Handle)
        : VPCtx(VPCtx), Handle(Handle) {}
    llvm::Value *operator*() const {
      unsigned Id = *Handle;
      return VPCtx->getScalar(Id);
    }

    value_iterator &operator++() {
      ++Handle;
      return *this;
    }

    bool operator!=(const value_iterator &It) { return Handle != It.Handle; }
  };

  llvm::iterator_range<value_iterator> iter_values(const llvm::BitVector &Ids) const {
    value_iterator Begin(this, Ids.set_bits_begin()),
        End(this, Ids.set_bits_end());
    return llvm::make_range(Begin, End);
  }
};

#endif // VECTOR_PACK_CONTEXT_H
