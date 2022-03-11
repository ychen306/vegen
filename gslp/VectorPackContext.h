#ifndef VECTOR_PACK_CONTEXT_H
#define VECTOR_PACK_CONTEXT_H

#include "InstSema.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/EquivalenceClasses.h"
#include "llvm/ADT/Hashing.h"
#include <vector>

class ReductionInfo;
class GammaNode;

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

class ControlCondition;
struct ConditionPack {
  // Categorize whether we can produce this pack as a vector of AND, OR, or
  // can't vectorize
  enum ConditionKind { CP_And, CP_Or, CP_Infeasible };
  ConditionKind Kind;
  llvm::SmallVector<const ControlCondition *, 4> Conds;

  const ConditionPack *Parent = nullptr; // For And
  const OperandPack *OP = nullptr;       // If this is an AND pack
  llvm::BitVector
      ElemsToFlip; // a mask indicating which elements of OP should be flipped;

  llvm::SmallVector<const ConditionPack *> CPs; // For Or
};

// VectorPackContext captures various meta data we use to create and manage
// vector packs. Basically we want to store vector packs are a bitvector, and we
// need this class to manage the mapping between a value and its integer id
struct VectorPackCache;
struct OperandPackCache;
class VectorPackContext {
  llvm::Function *F;
  std::vector<llvm::Value *> Scalars;
  llvm::DenseMap<llvm::Value *, unsigned> ScalarToIdMap;
  llvm::EquivalenceClasses<llvm::Value *> EquivalentValues;

  std::unique_ptr<VectorPackCache> PackCache;
  mutable llvm::DenseMap<llvm::ArrayRef<llvm::Value *>,
                         std::unique_ptr<OperandPack>>
      OperandCache;
  mutable llvm::DenseMap<std::pair<llvm::ArrayRef<const ControlCondition *>,
                                   const ControlCondition *>,
                         std::unique_ptr<ConditionPack>>
      ConditionPackCache;

  unsigned NumValues;

public:
  VectorPackContext(llvm::Function *F);
  ~VectorPackContext();

  void registerEquivalentValues(llvm::EquivalenceClasses<llvm::Value *> &&EC) {
    EquivalentValues = EC;
  }

  // Create a "General" vector pack
  VectorPack *createVectorPack(std::vector<const Operation::Match *> Matches,
                               llvm::BitVector Elements,
                               llvm::BitVector Depended,
                               const InstBinding *Producer,
                               llvm::TargetTransformInfo *TTI) const;

  // Create a vectorized load
  VectorPack *createLoadPack(llvm::ArrayRef<llvm::LoadInst *> Loads,
                             const ConditionPack *CP, llvm::BitVector Elements,
                             llvm::BitVector Depended,
                             llvm::TargetTransformInfo *TTI,
                             bool IsGather = false) const;

  // Create a vectorized store
  VectorPack *createStorePack(llvm::ArrayRef<llvm::StoreInst *> Stores,
                              const ConditionPack *CP, llvm::BitVector Elements,
                              llvm::BitVector Depended,
                              llvm::TargetTransformInfo *TTI,
                              bool IsScatter = false) const;

  // Create a vectorized phi
  VectorPack *createPhiPack(llvm::ArrayRef<llvm::PHINode *> PHIs,
                            llvm::BitVector Elements, llvm::BitVector Depended,
                            llvm::TargetTransformInfo *TTI) const;

  // Create a vectorized gamma
  VectorPack *createGammaPack(llvm::ArrayRef<const GammaNode *> Gammas,
                              llvm::BitVector Elements,
                              llvm::BitVector Depended,
                              llvm::TargetTransformInfo *TTI) const;

  // Create a vectorized comparison
  VectorPack *createCmpPack(llvm::ArrayRef<llvm::CmpInst *> Cmps,
                            llvm::BitVector Elements, llvm::BitVector Depended,
                            llvm::TargetTransformInfo *TTI) const;

  // Create a vectorized GEP
  VectorPack *createGEPPack(llvm::ArrayRef<llvm::GetElementPtrInst *> GEPs,
                            llvm::BitVector Elements, llvm::BitVector Depended,
                            llvm::TargetTransformInfo *TTI) const;
  // Create a simd pack
  VectorPack *createSIMDPack(llvm::ArrayRef<llvm::Instruction *> Insts,
                             llvm::BitVector Elements, llvm::BitVector Depended,
                             llvm::TargetTransformInfo *TTI) const;

  // Create a loop reduction pack
  VectorPack *
  createLoopReduction(const ReductionInfo &,
                  unsigned RdxLen /*vector length of the reduction*/,
                  llvm::TargetTransformInfo *TTI) const;

  // Create a loop free reduction
  VectorPack *
  createLoopFreeReduction(const ReductionInfo &, unsigned RdxLen,
      llvm::BitVector Depended,
      llvm::TargetTransformInfo *TTI) const;

  OperandPack *getCanonicalOperandPack(OperandPack OP) const;
  ConditionPack *getConditionPack(
      llvm::ArrayRef<const ControlCondition *>,
      llvm::Optional<const ControlCondition *> MaybeCommon = llvm::None) const;

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
    auto It = ScalarToIdMap.find(V);
    assert(It != ScalarToIdMap.end());
    return It->second;
  }

  void addInstruction(llvm::Instruction *);

  unsigned getNumValues() const { return NumValues; }

  llvm::Function *getFunction() const { return F; }

  // Fixme : templatize this to decouple use of bitvector
  class value_iterator : public std::iterator<std::forward_iterator_tag, typename llvm::Value *> {
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
    bool operator==(const value_iterator &It) { return Handle == It.Handle; }
  };

  llvm::iterator_range<value_iterator>
  iter_values(const llvm::BitVector &Ids) const {
    value_iterator Begin(this, Ids.set_bits_begin()),
        End(this, Ids.set_bits_end());
    return llvm::make_range(Begin, End);
  }
};

static bool is_drand48(llvm::Instruction *I) {
  using namespace llvm;
  auto *Call = dyn_cast<CallInst>(I);
  if (!Call)
    return false;
  auto *F = Call->getCalledFunction();
  return F && F->getName() == "drand48";
}

#endif // VECTOR_PACK_CONTEXT_H
