#ifndef VECTOR_PACK_H
#define VECTOR_PACK_H

#include "VectorPackContext.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/Analysis/VectorUtils.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instruction.h"
#include <set>

// A vector pack is an *ordered* set of values,
// these values should come from the same basic block
class VectorPack {

public:
  // Use this to model input operands
  using OperandPack = llvm::SmallVector<llvm::Value *, 8>;

  enum PackKind { General, Phi, Load, Store };

private:
  friend class VectorPackContext;
  friend struct VectorPackCache;

  const VectorPackContext *VPCtx;
  llvm::BitVector Elements;
  llvm::BitVector Depended;

  // FIXME just make VectorPack an interface
  //////////// Data for the 4 kinds
  PackKind Kind;
  // General
  const InstBinding *Producer = nullptr;
  llvm::SmallVector<const Operation::Match *, 4> Matches;
  // Load
  llvm::SmallVector<llvm::LoadInst *, 4> Loads;
  // Store
  llvm::SmallVector<llvm::StoreInst *, 4> Stores;
  // PHI
  llvm::SmallVector<llvm::PHINode *, 4> PHIs;
  ///////////////

  llvm::SmallVector<llvm::Value *, 4> OrderedValues;
  llvm::SmallVector<OperandPack, 4> OperandPacks;

  int Cost;

  void computeCost(llvm::TargetTransformInfo *TTI);

  // Constructor for a generic pack
  VectorPack(const VectorPackContext *VPCtx,
             llvm::ArrayRef<const Operation::Match *> Matches,
             llvm::BitVector Elements, llvm::BitVector Depended,
             const InstBinding *Producer, llvm::TargetTransformInfo *TTI)
      : VPCtx(VPCtx), Elements(Elements), Depended(Depended),
        Kind(PackKind::General), Producer(Producer),
        Matches(Matches.begin(), Matches.end()) {
    computeOperandPacks();
    computeOrderedValues();
    computeCost(TTI);
  }

  // Load Pack
  VectorPack(const VectorPackContext *VPCtx,
             llvm::ArrayRef<llvm::LoadInst *> Loads, llvm::BitVector Elements,
             llvm::BitVector Depended, llvm::TargetTransformInfo *TTI)
      : VPCtx(VPCtx), Elements(Elements), Depended(Depended),
        Kind(PackKind::Load), Loads(Loads.begin(), Loads.end()) {
    computeOperandPacks();
    computeOrderedValues();
    computeCost(TTI);
  }

  // Store Pack
  VectorPack(const VectorPackContext *VPCtx,
             llvm::ArrayRef<llvm::StoreInst *> Stores, llvm::BitVector Elements,
             llvm::BitVector Depended, llvm::TargetTransformInfo *TTI)
      : VPCtx(VPCtx), Elements(Elements), Depended(Depended),
        Kind(PackKind::Store), Stores(Stores.begin(), Stores.end()) {
    computeOperandPacks();
    computeOrderedValues();
    computeCost(TTI);
  }

  // Load Pack
  VectorPack(const VectorPackContext *VPCtx,
             llvm::ArrayRef<llvm::PHINode *> PHIs, llvm::BitVector Elements,
             llvm::BitVector Depended, llvm::TargetTransformInfo *TTI)
      : VPCtx(VPCtx), Elements(Elements), Depended(Depended),
        Kind(PackKind::Phi), PHIs(PHIs.begin(), PHIs.end()) {
    computeOperandPacks();
    computeOrderedValues();
    computeCost(TTI);
  }

  void computeOperandPacksForGeneral();
  void computeOperandPacksForLoad();
  void computeOperandPacksForStore();
  void computeOperandPacksForPhi();

  void computeOperandPacks();
  void computeOrderedValues();

  llvm::Value *emitVectorGeneral(llvm::ArrayRef<llvm::Value *> Operands,
                                 IntrinsicBuilder &Builder) const;
  llvm::Value *emitVectorLoad(llvm::ArrayRef<llvm::Value *> Operands,
                              IntrinsicBuilder &Builder) const;
  llvm::Value *emitVectorStore(llvm::ArrayRef<llvm::Value *> Operands,
                               IntrinsicBuilder &Builder) const;
  llvm::Value *emitVectorPhi(llvm::ArrayRef<llvm::Value *> Operands,
                             IntrinsicBuilder &Builder) const;

public:
  VectorPack(const VectorPack &Other) = default;
  VectorPack &operator=(const VectorPack &Other) = default;

  const InstBinding *getProducer() const {
    return (Kind == General) ? Producer : nullptr;
  }

  const VectorPackContext *getContext() const { return VPCtx; }

  llvm::iterator_range<VectorPackContext::value_iterator>
  elementValues() const {
    return VPCtx->iter_values(Elements);
  }

  llvm::iterator_range<VectorPackContext::value_iterator>
  dependedValues() const {
    return VPCtx->iter_values(Depended);
  }

  bool isStore() const { return Kind == Store; }

  llvm::BasicBlock *getBasicBlock() const { return VPCtx->getBasicBlock(); }

  llvm::ArrayRef<llvm::Value *> getOrderedValues() const {
    return OrderedValues;
  }

  unsigned numElements() const { return Elements.count(); }

  const llvm::BitVector &getDepended() const { return Depended; }

  const llvm::BitVector &getElements() const { return Elements; }

  llvm::ArrayRef<OperandPack> getOperandPacks() const { return OperandPacks; }

  llvm::Value *emit(llvm::ArrayRef<llvm::Value *> Operands,
                    IntrinsicBuilder &Builder) const;

  int getCost() const { return Cost; }

  // Choose a right place to gather an operand
  void setOperandGatherPoint(unsigned OperandId,
                             IntrinsicBuilder &Builder) const;
};

llvm::raw_ostream &operator<<(llvm::raw_ostream &OS, const VectorPack &VP);

llvm::Type *getVectorType(const VectorPack::OperandPack &OpndPack);

llvm::Type *getVectorType(const VectorPack &VP);

#endif // VECTOR_PACK_H
