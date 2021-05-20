#ifndef SOLVER_H
#define SOLVER_H

#include "CandidatePackSet.h"
#include "Packer.h"
#include "VectorPackContext.h"
#include "VectorPackSet.h"
#include "llvm/ADT/ArrayRef.h"
#include <bitset>

llvm::raw_ostream &operator<<(llvm::raw_ostream &, const OperandPack &);

class MatchManager;
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

  void freezeOneInst(llvm::Instruction *);

  // Check if `OP` has been resolved.
  bool resolved(const OperandPack &OP) const;

public:
  // Create the initial frontier, which surrounds the whole basic block
  Frontier(llvm::BasicBlock *BB, Packer *Pkr);
  void shrinkFor(llvm::BitVector R);
  llvm::BasicBlock *getBasicBlock() const { return BB; }
  float advance(llvm::Instruction *, llvm::TargetTransformInfo *);
  float advance(const VectorPack *, llvm::TargetTransformInfo *);
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

class VectorPackSet;
float optimizeBottomUp(VectorPackSet &, Packer *, llvm::BasicBlock *);

#endif
