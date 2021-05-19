#ifndef HEURISTIC_H
#define HEURISTIC_H

#include "CandidatePackSet.h"
#include "Packer.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseMapInfo.h"

class Frontier;

class Heuristic {
  llvm::DenseMap<const OperandPack *, float> OrderedCosts;
  llvm::DenseMap<std::vector<llvm::Value *>, float,
                 llvm::DenseMapInfo<llvm::ArrayRef<llvm::Value *>>>
      UnorderedCosts;
  llvm::DenseMap<llvm::Instruction *, float> ScalarCosts;

  Packer *Pkr;
  const VectorPackContext *VPCtx;
  const CandidatePackSet *Candidates;

  float getCost(const VectorPack *VP);
  float getCost(llvm::Instruction *);
  float getCost(const OperandPack *OP);
  float getCost(llvm::Value *);

public:
  Heuristic(Packer *Pkr, const VectorPackContext *VPCtx,
            const CandidatePackSet *Candidates)
      : Pkr(Pkr), VPCtx(VPCtx), Candidates(Candidates) {}
  float getCost(const Frontier *);
};

#endif // HEURISTIC_H
