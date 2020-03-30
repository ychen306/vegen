#ifndef VECTOR_PACK_SET_H
#define VECTOR_PACK_SET_H

/*
 * VectorPackSet manages a set of compatible vector packs and
 * is responsible for lowering a set of packs to LLVM IR.
 */

#include "VectorPack.h"

class LocalDependenceAnalysis;

class VectorPackSet {
protected:
  unsigned NumPacks;
  llvm::Function *F;
  std::vector<std::unique_ptr<VectorPack>> AllPacks;
  // FIXME : rename Packs to BB2Packs;
  llvm::DenseMap<llvm::BasicBlock *, std::vector<VectorPack *>> Packs;
  llvm::DenseMap<llvm::BasicBlock *, llvm::BitVector> PackedValues;
  llvm::DenseMap<llvm::Value *, VectorPack *> ValueToPackMap;

  // This tells us where a value is located in a pack
  struct VectorPackIndex {
    const VectorPack *VP;
    unsigned Idx;

    bool operator<(const VectorPackIndex &Other) const {
      return std::tie(VP, Idx) < std::tie(Other.VP, Other.Idx);
    }
  };

  // Mapping a value to the pack that produce them.
  using ValueIndexTy = llvm::DenseMap<const llvm::Value *, VectorPackIndex>;
  // Mapping VectorPack -> their materialized values.
  using PackToValueTy = llvm::DenseMap<const VectorPack *, llvm::Value *>;

  // Get the vector value representing OpndPack.
  static llvm::Value *gatherOperandPack(const VectorPack::OperandPack &OpndPack,
                                        const ValueIndexTy &ValueIndex,
                                        const PackToValueTy &MaterializedPacks,
                                        IntrinsicBuilder &Builder);

  // Clear auxiliary data structure storing a vector pack
  void removeAux(VectorPack *);

  void copy(const VectorPackSet &Other);

  void add(std::unique_ptr<VectorPack> VP);

public:
  VectorPackSet(const VectorPackSet &Other) { copy(Other); }
  VectorPackSet(llvm::Function *F) : NumPacks(0), F(F) {}

  VectorPackSet &operator=(const VectorPackSet &Other) {
    copy(Other);
    return *this;
  }

  unsigned getNumPacks() const { return NumPacks; }

  bool isPacked(llvm::Instruction *, const VectorPackContext &) const;

  bool isCompatibleWith(const VectorPack &VP) const;

  // Add VP to this set if it doesn't conflict with existing packs.
  // return if successful
  bool tryAdd(std::unique_ptr<VectorPack> VP);

  // Remove the one we just add
  void pop();

  // Estimate cost of this pack
  float getCostSaving(llvm::TargetTransformInfo *TTI,
                      llvm::BlockFrequencyInfo *BFI) const;

  // Generate vector code from the packs
  void codegen(IntrinsicBuilder &Builder,
               llvm::DenseMap<llvm::BasicBlock *,
                              std::unique_ptr<LocalDependenceAnalysis>> &LDAs);

  VectorPack &getPack(unsigned i) {
    assert(i < NumPacks);
    return *AllPacks[i];
  }
};

#endif // end VECTOR_PACK_SET_H
