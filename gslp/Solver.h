#ifndef SOLVER_H
#define SOLVER_H

#include "llvm/ADT/DenseSet.h"
#include <vector>

namespace llvm {
class BasicBlock;
}

class VectorPack;

struct CandidatePackSet {
  std::vector<const VectorPack *> Packs;
  std::vector<std::vector<const VectorPack *>> Inst2Packs;
};

class Packer;
class VectorPackSet;
float optimizeBottomUp(
    std::vector<const VectorPack *> &, Packer *,
    llvm::DenseSet<llvm::BasicBlock *> *BlocksToIgnore = nullptr);
float optimizeBottomUp(VectorPackSet &, Packer *);

#endif
