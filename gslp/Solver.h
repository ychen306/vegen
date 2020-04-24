#ifndef SOLVER_H
#define SOLVER_H

#include "VectorPackContext.h"
#include "VectorPackSet.h"
#include "llvm/ADT/ArrayRef.h"
#include <bitset>

// A lightweight wrapper around VectorPack::OperandPack
// to track resolved lanes (lanes with known producers)
struct UnresolvedOperandPack {
  using BitsetTy = std::bitset<64>;

  const VectorPack::OperandPack *Pack;
  BitsetTy ResolvedLanes;

  UnresolvedOperandPack(UnresolvedOperandPack &&) = default;
  UnresolvedOperandPack &operator=(UnresolvedOperandPack &&) = default;

  UnresolvedOperandPack(const VectorPack::OperandPack &Pack) : Pack(&Pack) {
    for (unsigned i = 0; i < Pack.size(); i++) {
      if (llvm::isa<llvm::Constant>(Pack[i]))
        ResolvedLanes.set(i);
    }
  }

  void resolveOneLane(unsigned i) { ResolvedLanes.set(i); }
  bool resolved() const { return ResolvedLanes.all(); }
  bool operator<(const UnresolvedOperandPack &Other) const {
    auto RL = ResolvedLanes.to_ullong();
    auto RL2 = ResolvedLanes.to_ullong();
    return std::tie(Pack, RL) < std::tie(Other.Pack, RL2);
  }
};

class Frontier {
  llvm::BasicBlock *BB;
  const VectorPackContext *VPCtx;
  llvm::BasicBlock::reverse_iterator BBIt;
  std::vector<UnresolvedOperandPack> UnresolvedPacks;
  std::vector<bool> UnresolvedScalars;
  // Instructions we haven't assigned yet.
  std::vector<bool> FreeInsts;

  void freezeOneInst(unsigned);
  bool resolveOperandPack(const VectorPack &VP, UnresolvedOperandPack &UP);
  void advanceBBIt();
  bool isFreeInst(llvm::Instruction *I) {
    return FreeInsts[VPCtx->getScalarId(I)];
  }

public:
  // Create the initial frontier, which surrounds the whole basic block
  Frontier(llvm::BasicBlock *BB, const VectorPackContext *VPCtx);

  bool operator<(const Frontier &Other) const {
    auto CmpKey = [](const Frontier &Frt) {
      return std::tie(Frt.FreeInsts, Frt.UnresolvedScalars,
                      Frt.UnresolvedPacks);
    };
    return CmpKey(*this) < CmpKey(Other);
  }
  Frontier advance(const VectorPack *, float &Cost, llvm::TargetTransformInfo *TTI) const;
  Frontier advance(llvm::Instruction *, float &Cost, llvm::TargetTransformInfo *TTI) const;
  llvm::Instruction *getNextFreeInst() const;
};
#endif
