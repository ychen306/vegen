#ifndef SOLVER_H
#define SOLVER_H

#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/ArrayRef.h"
#include <vector>

namespace llvm {
class BasicBlock;
}

class VectorPack;
class OperandPack;
class Heuristic;
class Plan;

struct CandidatePackSet {
  std::vector<const VectorPack *> Packs;
  std::vector<std::vector<const VectorPack *>> Inst2Packs;
};

class Packer;
class VectorPackSet;
float optimizeBottomUp(
    std::vector<const VectorPack *> &, Packer *,
    llvm::ArrayRef<const OperandPack *> SeedOperands={},
    llvm::DenseSet<llvm::BasicBlock *> *BlocksToIgnore = nullptr);
float optimizeBottomUp(VectorPackSet &, Packer *, llvm::ArrayRef<const OperandPack *> SeedOperands={});

void runBottomUpFromOperand(const OperandPack *OP, Plan &P, Heuristic &H);

#endif
