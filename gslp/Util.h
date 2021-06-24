#ifndef UTIL_H
#define UTIL_H

#include "VectorPack.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallPtrSet.h"

namespace llvm {
class Instruction;
class Value;
}

// Mapping a load/store -> a set of consecutive loads/stores
//
// This is basically a generalization of a store/load chain.
// We use a DAG because a load, for example, might have multiple
// "next" candidate.
using ConsecutiveAccessDAG =
    llvm::DenseMap<llvm::Instruction *,
                   llvm::SmallPtrSet<llvm::Instruction *, 4>>;

static unsigned getBitWidth(llvm::Value *V) {
  auto *Ty = V->getType();
  if (Ty->isIntegerTy())
    return Ty->getIntegerBitWidth();
  if (Ty->isFloatTy())
    return 32;
  if (Ty->isDoubleTy())
    return 64;
  llvm_unreachable("unsupported value type");
}

#endif // UTIL_H
