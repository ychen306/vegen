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

template <typename T>
T &choose(std::vector<T> &Xs) {
  return Xs[rand_int(Xs.size())];
}

template <typename InstTy>
llvm::Optional<llvm::SmallVector<InstTy *, 4>>
castOperandPack(const VectorPack::OperandPack &OpndPack) {
  using namespace llvm;
  SmallVector<InstTy *, 4> Ret;
  for (auto *V : OpndPack) {
    auto *I = dyn_cast<InstTy>(V);
    if (!I)
      return None;
    Ret.push_back(I);
  }
  return Ret;
}

static inline bool isScalarType(llvm::Type *Ty) {
  return Ty->getScalarType() == Ty;
}

static inline bool isFloat(llvm::Instruction::BinaryOps Opcode) {
  using namespace llvm;
  switch (Opcode) {
  case Instruction::FAdd:
  case Instruction::FSub:
  case Instruction::FMul:
  case Instruction::FDiv:
  case Instruction::FRem:
    return true;
  default:
    return false;
  }
}

#endif // UTIL_H
