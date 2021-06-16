#ifndef SOLVER_H
#define SOLVER_H

#include "VectorPackContext.h"
#include "llvm/ADT/ArrayRef.h"

llvm::raw_ostream &operator<<(llvm::raw_ostream &, const OperandPack &);

struct CandidatePackSet {
  std::vector<const VectorPack *> Packs;
  std::vector<std::vector<const VectorPack *>> Inst2Packs;
};

class Packer;
class VectorPackSet;
float optimizeBottomUp(VectorPackSet &, Packer *, llvm::BasicBlock *);

#endif
