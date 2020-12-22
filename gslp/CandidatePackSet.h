#ifndef CANDIDATE_PACK_SET
#define CANDIDATE_PACK_SET

#include "llvm/ADT/BitVector.h"
#include <vector>

class VectorPack;

struct CandidatePackSet {
  std::vector<const VectorPack *> Packs;
  llvm::BitVector Members;
  std::vector<std::vector<const VectorPack *>> Inst2Packs;
};

#endif // CANDIDATE_PACK_SET
