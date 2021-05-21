#ifndef SOLVER_H
#define SOLVER_H

#include "VectorPackContext.h"
#include "llvm/ADT/ArrayRef.h"

llvm::raw_ostream &operator<<(llvm::raw_ostream &, const OperandPack &);

class Packer;
class Heuristic;

class Frontier {
  Packer *Pkr;
  llvm::BasicBlock *BB;
  const VectorPackContext *VPCtx;
  std::vector<const OperandPack *> UnresolvedPacks;
  llvm::BitVector UnresolvedScalars;
  // Instructions we haven't assigned yet.
  llvm::BitVector FreeInsts;
  // Free insts without free users
  llvm::BitVector UsableInsts;
  float Est;

  void freezeOneInst(llvm::Instruction *, Heuristic *);

  // Check if `OP` has been resolved.
  bool resolved(const OperandPack &OP) const;

public:
  float getEstimatedCost() const { return Est; }
  // Create the initial frontier, which surrounds the whole basic block
  Frontier(llvm::BasicBlock *BB, Packer *Pkr, Heuristic *);
  llvm::BasicBlock *getBasicBlock() const { return BB; }
  float advance(llvm::Instruction *, llvm::TargetTransformInfo *, Heuristic *);
  float advance(const VectorPack *, llvm::TargetTransformInfo *, Heuristic *);
  const llvm::BitVector &getFreeInsts() const { return FreeInsts; }
  bool isFree(llvm::Instruction *I) const {
    return FreeInsts.test(VPCtx->getScalarId(I));
  }
  llvm::ArrayRef<const OperandPack *> getUnresolvedPacks() const {
    return UnresolvedPacks;
  }
  llvm::iterator_range<VectorPackContext::value_iterator>
  getUnresolvedScalars() const {
    return VPCtx->iter_values(UnresolvedScalars);
  }
  unsigned numUnresolvedScalars() const { return UnresolvedScalars.count(); }
  Packer *getPacker() const { return Pkr; }
  bool isUsable(llvm::Instruction *I) const {
    // FIXME: deal with PHINode properly
    if (llvm::isa<llvm::PHINode>(I))
      return isFree(I);
    return UsableInsts.test(VPCtx->getScalarId(I));
  }

  llvm::iterator_range<VectorPackContext::value_iterator> usableInsts() const {
    return VPCtx->iter_values(UsableInsts);
  }
  const llvm::BitVector &usableInstIds() const { return UsableInsts; }

  unsigned numUsableInsts() const { return UsableInsts.count(); }
  const VectorPackContext *getContext() const { return VPCtx; }
};

struct CandidatePackSet {
  std::vector<const VectorPack *> Packs;
  std::vector<std::vector<const VectorPack *>> Inst2Packs;
};

class VectorPackSet;
float optimizeBottomUp(VectorPackSet &, Packer *, llvm::BasicBlock *);

#endif
