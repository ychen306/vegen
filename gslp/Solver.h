#ifndef SOLVER_H
#define SOLVER_H

#include "CandidatePackSet.h"
#include "Packer.h"
#include "VectorPackContext.h"
#include "VectorPackSet.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/Hashing.h"
#include <bitset>

llvm::raw_ostream &operator<<(llvm::raw_ostream &, const OperandPack &);

class MatchManager;
class Frontier {
  Packer *Pkr;
  friend struct FrontierHashInfo;
  llvm::BasicBlock *BB;
  const VectorPackContext *VPCtx;
  std::vector<const OperandPack *> UnresolvedPacks;
  llvm::BitVector UnresolvedScalars;
  // Instructions we haven't assigned yet.
  llvm::BitVector FreeInsts;
  // Free insts without free users
  llvm::BitVector UsableInsts;

  void freezeOneInst(llvm::Instruction *);
  bool resolveOperandPack(const VectorPack &VP, const OperandPack &UP);

  // Check if `OP` has been resolved.
  bool resolved(const OperandPack &OP) const;
  unsigned Hash;

public:
  // Create the initial frontier, which surrounds the whole basic block
  Frontier(llvm::BasicBlock *BB, Packer *Pkr);
  std::unique_ptr<Frontier> advance(const VectorPack *VP, float &Cost,
                                    llvm::TargetTransformInfo *TTI) const;
  std::unique_ptr<Frontier> advance(llvm::Instruction *I, float &Cost,
                                    llvm::TargetTransformInfo *TTI) const;
  void shrinkFor(llvm::BitVector R);
  llvm::BasicBlock *getBasicBlock() const { return BB; }
  float advanceInplace(llvm::Instruction *, llvm::TargetTransformInfo *);
  float advanceInplace(const VectorPack *, llvm::TargetTransformInfo *);
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

// Hashing support for `Frontier`
struct FrontierHashInfo {
  static Frontier *getEmptyKey() { return nullptr; }

  static Frontier *getTombstoneKey() { return reinterpret_cast<Frontier *>(1); }

  static unsigned getHashValue(const Frontier *Frt) {
    using namespace llvm;
#if 1

    if (Frt == getEmptyKey()) {
      return ~0;
    } else if (Frt == getTombstoneKey()) {
      return ~1;
    }
    return Frt->Hash;
#else
    if (Frt == getEmptyKey()) {
      return hash_combine(reinterpret_cast<BasicBlock *>(0),
                          ArrayRef<uint64_t>(), ArrayRef<uint64_t>(),
                          ArrayRef<const OperandPack *>());
    } else if (Frt == getTombstoneKey()) {
      return hash_combine(reinterpret_cast<BasicBlock *>(1),
                          ArrayRef<uint64_t>(), ArrayRef<uint64_t>(),
                          ArrayRef<const OperandPack *>());
    }

    return hash_combine(reinterpret_cast<BasicBlock *>(2),
                        Frt->UnresolvedScalars.getData(),
                        Frt->FreeInsts.getData(),
                        ArrayRef<const OperandPack *>(Frt->UnresolvedPacks));
#endif
  }

  static bool isTombstoneOrEmpty(const Frontier *Frt) {
    return Frt == getTombstoneKey() || Frt == getEmptyKey();
  }

  static bool isEqual(const Frontier *A, const Frontier *B) {
    if (isTombstoneOrEmpty(A) || isTombstoneOrEmpty(B))
      return A == B;

    return A->BB == B->BB && A->FreeInsts == B->FreeInsts &&
           A->UnresolvedScalars == B->UnresolvedScalars &&
           A->UsableInsts == B->UsableInsts &&
           A->UnresolvedPacks == B->UnresolvedPacks;
  }
};

class VectorPackSet;
float optimizeBottomUp(VectorPackSet &, Packer *, llvm::BasicBlock *);

#endif
