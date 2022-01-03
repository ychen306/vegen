#ifndef VECTOR_PACK_H
#define VECTOR_PACK_H

#include "Reduction.h"
#include "VectorPackContext.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instruction.h"
#include <set>

// Phi node with incoming blocks replaced with explicit control conditions
class GammaNode;

// A vector pack is an *ordered* set of values,
// these values should come from the same basic block
class VectorPack {
public:
  friend llvm::raw_ostream &operator<<(llvm::raw_ostream &OS,
                                       const VectorPack &VP);

  enum PackKind { General, Phi, Load, Store, Reduction, GEP, Gamma, Cmp };

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
  bool IsGatherScatter = false;
  // Load
  llvm::SmallVector<llvm::LoadInst *, 4> Loads;
  // Store
  llvm::SmallVector<llvm::StoreInst *, 4> Stores;
  // PHI
  llvm::SmallVector<llvm::PHINode *, 4> PHIs;
  // Gated PHI (i.e., divergent PHIs that we will lower into vector select
  llvm::SmallVector<const GammaNode *, 4> Gammas;
  // Loop reduction
  llvm::Optional<ReductionInfo> Rdx;
  unsigned RdxLen;
  // GEP
  llvm::SmallVector<llvm::GetElementPtrInst *, 4> GEPs;
  llvm::SmallVector<llvm::CmpInst *, 4> Cmps;
  ///////////////

  // For side-effectul packs like loads and stores
  const ConditionPack *CP = nullptr;

  llvm::SmallVector<llvm::Value *, 4> OrderedValues;
  llvm::SmallVector<const OperandPack *, 4> OperandPacks;

  int Cost;
  int ProducingCost;

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
  VectorPack(const VectorPackContext *VPCtx, bool IsGatherScatter,
             const ConditionPack *CP, llvm::ArrayRef<llvm::LoadInst *> Loads,
             llvm::BitVector Elements, llvm::BitVector Depended,
             llvm::TargetTransformInfo *TTI)
      : VPCtx(VPCtx), Elements(Elements), Depended(Depended),
        Kind(PackKind::Load), IsGatherScatter(IsGatherScatter), CP(CP),
        Loads(Loads.begin(), Loads.end()) {
    computeOperandPacks();
    computeOrderedValues();
    computeCost(TTI);
  }

  // Store Pack
  VectorPack(const VectorPackContext *VPCtx, bool IsGatherScatter,
             const ConditionPack *CP, llvm::ArrayRef<llvm::StoreInst *> Stores,
             llvm::BitVector Elements, llvm::BitVector Depended,
             llvm::TargetTransformInfo *TTI)
      : VPCtx(VPCtx), Elements(Elements), Depended(Depended),
        Kind(PackKind::Store), IsGatherScatter(IsGatherScatter), CP(CP),
        Stores(Stores.begin(), Stores.end()) {
    computeOperandPacks();
    computeOrderedValues();
    computeCost(TTI);
  }

  // PHI Pack
  VectorPack(const VectorPackContext *VPCtx,
             llvm::ArrayRef<llvm::PHINode *> PHIs, llvm::BitVector Elements,
             llvm::BitVector Depended, llvm::TargetTransformInfo *TTI)
      : VPCtx(VPCtx), Elements(Elements), Depended(Depended),
        Kind(PackKind::Phi), PHIs(PHIs.begin(), PHIs.end()) {
    computeOperandPacks();
    computeOrderedValues();
    computeCost(TTI);
  }

  // Reduction
  VectorPack(const VectorPackContext *VPCtx, ReductionInfo RI, unsigned RdxLen,
             llvm::BitVector Elements, llvm::BitVector Depended,
             llvm::TargetTransformInfo *TTI)
      : VPCtx(VPCtx), Elements(Elements), Depended(Depended),
        Kind(PackKind::Reduction), Rdx(RI), RdxLen(RdxLen) {
    computeOperandPacks();
    computeOrderedValues();
    computeCost(TTI);
  }

  // GEP Pack
  VectorPack(const VectorPackContext *VPCtx,
             llvm::ArrayRef<llvm::GetElementPtrInst *> GEPs,
             llvm::BitVector Elements, llvm::BitVector Depended,
             llvm::TargetTransformInfo *TTI)
      : VPCtx(VPCtx), Elements(Elements), Depended(Depended),
        Kind(PackKind::GEP), GEPs(GEPs.begin(), GEPs.end()) {
    computeOperandPacks();
    computeOrderedValues();
    computeCost(TTI);
  }

  // Gated PHI Pack
  VectorPack(const VectorPackContext *VPCtx,
             llvm::ArrayRef<const GammaNode *> Gammas, llvm::BitVector Elements,
             llvm::BitVector Depended, llvm::TargetTransformInfo *TTI)
      : VPCtx(VPCtx), Elements(Elements), Depended(Depended),
        Kind(PackKind::Gamma), Gammas(Gammas.begin(), Gammas.end()) {
    computeOperandPacks();
    computeOrderedValues();
    computeCost(TTI);
  }

  // Cmp pack
  VectorPack(const VectorPackContext *VPCtx,
             llvm::ArrayRef<llvm::CmpInst *> Cmps, llvm::BitVector Elements,
             llvm::BitVector Depended, llvm::TargetTransformInfo *TTI)
      : VPCtx(VPCtx), Elements(Elements), Depended(Depended),
        Kind(PackKind::Cmp), Cmps(Cmps.begin(), Cmps.end()) {
    computeOperandPacks();
    computeOrderedValues();
    computeCost(TTI);
  }

  std::vector<OperandPack> computeOperandPacksForGeneral();
  std::vector<OperandPack> computeOperandPacksForLoad();
  std::vector<OperandPack> computeOperandPacksForStore();
  std::vector<OperandPack> computeOperandPacksForPhi();

  void canonicalizeOperandPacks(llvm::ArrayRef<OperandPack> OPs) {
    for (auto &OP : OPs)
      OperandPacks.push_back(VPCtx->getCanonicalOperandPack(std::move(OP)));
  }

  void computeOperandPacks();
  void computeOrderedValues();

  llvm::Value *emitVectorGeneral(llvm::ArrayRef<llvm::Value *> Operands,
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
  llvm::Value *emitVectorLoad(llvm::ArrayRef<llvm::Value *> Operands,
                              llvm::Value *Mask,
                              std::function<llvm::Value *(llvm::Value *)> GetScalar,
                              IntrinsicBuilder &Builder) const;
  llvm::Value *emitVectorStore(llvm::ArrayRef<llvm::Value *> Operands,
                               llvm::Value *Mask,
                               std::function<llvm::Value *(llvm::Value *)> GetScalar,
                               IntrinsicBuilder &Builder) const;

  bool isStore() const { return Kind == Store; }
  bool isLoad() const { return Kind == Load; }
  bool isCmp() const { return Kind == Cmp; }
  bool isGEP() const { return Kind == GEP; }
  bool isPHI() const { return Kind == Phi; }
  bool isGamma() const { return Kind == Gamma; }
  bool isReduction() const { return Rdx.hasValue(); }
  const ReductionInfo &getReductionInfo() const {
    assert(isReduction());
    return *Rdx;
  };
  llvm::ArrayRef<const GammaNode *> getGammas() const {
    assert(isGamma());
    return Gammas;
  }

  // Get the pointer of a *consecutive* load or store pack
  llvm::Value *getLoadStorePointer() const;

  llvm::ArrayRef<llvm::Value *> getOrderedValues() const {
    return OrderedValues;
  }

  unsigned numElements() const { return Elements.count(); }

  const llvm::BitVector &getDepended() const { return Depended; }

  const llvm::BitVector &getElements() const { return Elements; }

  llvm::ArrayRef<const OperandPack *> getOperandPacks() const {
    return OperandPacks;
  }

  llvm::Value *emit(llvm::ArrayRef<llvm::Value *> Operands,
                    IntrinsicBuilder &Builder) const;

  int getCost() const { return Cost; }
  int getProducingCost() const { return ProducingCost; }

  // Choose a right place to gather an operand
  void setOperandGatherPoint(unsigned OperandId,
                             IntrinsicBuilder &Builder) const;

  void
  getPackedInstructions(llvm::SmallPtrSetImpl<llvm::Instruction *> &) const;
};

llvm::FixedVectorType *getVectorType(const OperandPack &OpndPack);

llvm::FixedVectorType *getVectorType(const VectorPack &VP);

bool isConstantPack(const OperandPack &OpndPack);

llvm::raw_ostream &operator<<(llvm::raw_ostream &, const OperandPack &);

void getOperandPacksFromCondition(
    const ConditionPack *CP, llvm::SmallVectorImpl<const OperandPack *> &OPs);

#endif // VECTOR_PACK_H
