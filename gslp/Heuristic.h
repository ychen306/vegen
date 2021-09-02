#ifndef HEURISTIC_H
#define HEURISTIC_H

#include "llvm/ADT/DenseMap.h"
#include <map>

class Packer;
class VectorPack;
class VectorPackContext;
class OperandPack;
class CandidatePackSet;

namespace llvm {
class Value;
class Instruction;
class BasicBlock;
} // namespace llvm

class Heuristic {
public:
  struct Solution {
    float Cost;
    llvm::SmallVector<const VectorPack *, 2> Packs;
    bool Valid;

    Solution() : Valid(false) {}
    Solution(float Cost) : Cost(Cost), Valid(true) {}
    Solution(float Cost, llvm::ArrayRef<const VectorPack *> Packs)
        : Cost(Cost), Packs(Packs.begin(), Packs.end()), Valid(true) {}
    Solution(float Cost, const VectorPack *VP)
        : Cost(Cost), Packs({VP}), Valid(true) {}
    Solution &operator=(const Solution &) = default;

    void update(const Solution &New) {
      if (!Valid || Cost > New.Cost)
        *this = New;
    }
  };

private:
  llvm::DenseMap<const OperandPack *, Solution> Solutions;
  llvm::DenseMap<llvm::Instruction *, float> ScalarCosts;

  Packer *Pkr;
  const CandidatePackSet *Candidates;
  float getCost(const VectorPack *VP);

public:
  Heuristic(Packer *Pkr, const CandidatePackSet *Candidates)
      : Pkr(Pkr), Candidates(Candidates) {}
  float getCost(const OperandPack *OP) { return solve(OP).Cost; }
  float getCost(llvm::Value *);
  Solution solve(const OperandPack *OP);
};

#endif // HEURISTIC_H
