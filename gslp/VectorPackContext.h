#ifndef VECTOR_PACK_CONTEXT_H
#define VECTOR_PACK_CONTEXT_H

#include "InstSema.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/Hashing.h"
#include <vector>

class VectorPack;
struct OperandProducerInfo {
  bool Feasible; // Whether it's feasible to produce this operand pack
  llvm::BitVector Elements;
  llvm::SmallVector<VectorPack *, 4> Producers;
  llvm::SmallVector<VectorPack *, 2> LoadProducers;
  llvm::ArrayRef<VectorPack *> getProducers() const {
    if (!Producers.empty())
      return Producers;
    return LoadProducers;
  }
};

// Use this to model input operands
struct OperandPack : public llvm::SmallVector<llvm::Value *, 8> {
  mutable bool OPIValid = false;
  mutable OperandProducerInfo OPI;
  mutable llvm::FixedVectorType *Ty = nullptr;
};

// VectorPackContext captures various meta data we use to create and manage
// vector packs. Basically we want to store vector packs are a bitvector, and we
// need this class to manage the mapping between a value and its integer id
class VectorPack;
struct VectorPackCache;
struct OperandPackCache;
class VectorPackContext {
  llvm::BasicBlock *BB;
  std::vector<llvm::Value *> Scalars;
  llvm::DenseMap<llvm::Value *, unsigned> ScalarToIdMap;

  std::unique_ptr<VectorPackCache> PackCache;
  mutable llvm::DenseMap<llvm::ArrayRef<llvm::Value *>,
                         std::unique_ptr<OperandPack>>
      OperandCache;

public:
  VectorPackContext(llvm::BasicBlock *BB);
  ~VectorPackContext();

  // Create a "General" vector pack
  VectorPack *createVectorPack(std::vector<const Operation::Match *> Matches,
                               llvm::BitVector Elements,
                               llvm::BitVector Depended,
                               const InstBinding *Producer,
                               llvm::TargetTransformInfo *TTI) const;

  // Create a vectorized load
  VectorPack *createLoadPack(llvm::ArrayRef<llvm::LoadInst *> Loads,
                             llvm::BitVector Elements, llvm::BitVector Depended,
                             llvm::TargetTransformInfo *TTI) const;

  // Create a vectorized store
  VectorPack *createStorePack(llvm::ArrayRef<llvm::StoreInst *> Stores,
                              llvm::BitVector Elements,
                              llvm::BitVector Depended,
                              llvm::TargetTransformInfo *TTI) const;

  // Create a vectorized phi
  VectorPack *createPhiPack(llvm::ArrayRef<llvm::PHINode *> PHIs,
                            llvm::TargetTransformInfo *TTI) const;

  // TODO: clean this up...
  OperandPack *getCanonicalOperandPack(OperandPack OP) const {
    auto It = OperandCache.find(OP);
    if (It != OperandCache.end())
      return It->second.get();
    auto NewOP = std::make_unique<OperandPack>(OP);
    return (OperandCache[*NewOP] = std::move(NewOP)).get();
  }

  // Remove duplicate elements in OP
  const OperandPack *dedup(const OperandPack *) const;
  const OperandPack *even(const OperandPack *) const;
  const OperandPack *odd(const OperandPack *) const;

  llvm::Value *getScalar(unsigned Id) const {
    assert(Id < Scalars.size());
    return Scalars[Id];
  }

  bool isKnownValue(const llvm::Value *V) const {
    return ScalarToIdMap.count(V);
  }

  unsigned getScalarId(const llvm::Value *V) const {
    assert(llvm::cast<llvm::Instruction>(V)->getParent() == BB);
    auto It = ScalarToIdMap.find(V);
    assert(It != ScalarToIdMap.end());
    return It->second;
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

  llvm::iterator_range<value_iterator>
  iter_values(const llvm::BitVector &Ids) const {
    value_iterator Begin(this, Ids.set_bits_begin()),
        End(this, Ids.set_bits_end());
    return llvm::make_range(Begin, End);
  }
};

#endif // VECTOR_PACK_CONTEXT_H
