#ifndef SOLVER_H
#define SOLVER_H

#include <vector>

class VectorPack;

struct CandidatePackSet {
  std::vector<const VectorPack *> Packs;
  std::vector<std::vector<const VectorPack *>> Inst2Packs;
};

class Packer;
class VectorPackSet;
float optimizeBottomUp(VectorPackSet &, Packer *);

#endif
