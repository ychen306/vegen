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

  const VectorPackContext *VPCtx;
  llvm::BitVector Elements;
  llvm::BitVector Depended;

  // FIXME just make VectorPack an interface
  //////////// Data for the 4 kinds
  PackKind Kind;
  // General
  std::vector<Operation::Match> Matches;
  const InstBinding *Producer;
  // Load
  std::vector<llvm::LoadInst *> Loads;
  // Store
  std::vector<llvm::StoreInst *> Stores;
  // PHI
  std::vector<llvm::PHINode *> PHIs;
  ///////////////

  // Constructor for a generic pack
  VectorPack(const VectorPackContext *VPCtx,
             llvm::ArrayRef<Operation::Match> Matches, llvm::BitVector Elements,
             llvm::BitVector Depended, const InstBinding *Producer)
      : VPCtx(VPCtx), Elements(Elements), Depended(Depended),
        Kind(PackKind::General), Producer(Producer), Matches(Matches) {}

  // Load Pack
  VectorPack(const VectorPackContext *VPCtx,
             llvm::ArrayRef<llvm::LoadInst *> Loads, llvm::BitVector Elements,
             llvm::BitVector Depended)
      : VPCtx(VPCtx), Elements(Elements), Depended(Depended),
        Kind(PackKind::Load), Loads(Loads) {}

  // Store Pack
  VectorPack(const VectorPackContext *VPCtx,
             llvm::ArrayRef<llvm::StoreInst *> Stores, llvm::BitVector Elements,
             llvm::BitVector Depended)
      : VPCtx(VPCtx), Elements(Elements), Depended(Depended),
        Kind(PackKind::Store), Stores(Stores) {}

  // Load Pack
  VectorPack(const VectorPackContext *VPCtx,
             llvm::ArrayRef<llvm::PHINode *> PHIs, llvm::BitVector Elements,
             llvm::BitVector Depended)
      : VPCtx(VPCtx), Elements(Elements), Depended(Depended),
        Kind(PackKind::Phi), PHIs(PHIs) {}

  std::vector<OperandPack> getOperandPacksForGeneral() const;
  std::vector<OperandPack> getOperandPacksForLoad() const;
  std::vector<OperandPack> getOperandPacksForStore() const;
  std::vector<OperandPack> getOperandPacksForPhi() const;

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

  llvm::BasicBlock *getBasicBlock() const { return VPCtx->getBasicBlock(); }

  std::vector<llvm::Value *> getOrderedValues() const;

  unsigned numElements() const { return Elements.count(); }

  const llvm::BitVector &getDepended() const { return Depended; }

  const llvm::BitVector &getElements() const { return Elements; }

  const std::vector<OperandPack> getOperandPacks() const;

  llvm::Value *emit(llvm::ArrayRef<llvm::Value *> Operands,
                    IntrinsicBuilder &Builder) const;

  int getCost(llvm::TargetTransformInfo *TTI, llvm::LLVMContext &Ctx) const;

  // Choose a right place to gather an operand
  void setOperandGatherPoint(unsigned OperandId,
                             IntrinsicBuilder &Builder) const;
};

llvm::raw_ostream &operator<<(llvm::raw_ostream &OS, const VectorPack &VP);

#endif // VECTOR_PACK_H
