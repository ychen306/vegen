#ifndef EXPR_HASHER_H
#define EXPR_HASHER_H

#include "llvm/ADT/DenseMap.h"
#include "llvm/Support/RandomNumberGenerator.h"

namespace llvm {
class Instruction;
class Type;
class Value;
}


class ExpressionHasher {
public:
  using HashType = uint64_t;
private:
  std::unique_ptr<llvm::RandomNumberGenerator> RNG;
  llvm::DenseMap<unsigned, HashType> OpcodeHashes;
  llvm::DenseMap<llvm::Type *, HashType> LeafHashes;
  llvm::DenseMap<llvm::Instruction *, HashType> InstHashes;

  HashType hashLeaf(llvm::Type *);
  HashType hashOpcode(unsigned Opcode);
  HashType hashValue(llvm::Value *);
public:
  ExpressionHasher(decltype(RNG) RNG) : RNG(std::move(RNG)) {}
  HashType hash(llvm::Instruction *);
};

#endif // end EXPR_HASHER_H
