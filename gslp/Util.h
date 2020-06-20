#ifndef UTIL_H
#define UTIL_H

#include "VectorPack.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallPtrSet.h"

namespace llvm {
class Instruction;
}

// Mapping a load/store -> a set of consecutive loads/stores
//
// This is basically a generalization of a store/load chain.
// We use a DAG because a load, for example, might have multiple
// "next" candidate.
using ConsecutiveAccessDAG =
    llvm::DenseMap<llvm::Instruction *,
                   llvm::SmallPtrSet<llvm::Instruction *, 4>>;

// Sample an integer between 0 and N.
static inline unsigned rand_int(int N) { return std::rand() % N; }

// Remove elements indexed by `ToRemove`, which is sorted in increasing order.
template <typename T>
void remove(std::vector<T> &X, llvm::ArrayRef<unsigned> ToRemove) {
  for (unsigned i : llvm::make_range(ToRemove.rbegin(), ToRemove.rend())) {
    std::swap(X[i], X.back());
    X.pop_back();
  }
}

#endif // UTIL_H
