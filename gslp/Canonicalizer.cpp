#include "Canonicalizer.h"
#include "llvm/ADT/Hashing.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"

using namespace llvm;

ExpressionHasher::HashType ExpressionHasher::hashLeaf(Type *Ty) {
  if (LeafHashes.count(Ty))
    return LeafHashes[Ty];
  return LeafHashes[Ty] = (*RNG)();
}

ExpressionHasher::HashType ExpressionHasher::hashOpcode(unsigned Opcode) {
  if (OpcodeHashes.count(Opcode))
    return OpcodeHashes[Opcode];
  return OpcodeHashes[Opcode] = (*RNG)();
}

ExpressionHasher::HashType ExpressionHasher::hashValue(Value *V) {
  if (isa<BinaryOperator>(V) || isa<SelectInst>(V) ||
      isa<CastInst>(V) || isa<CmpInst>(V) || isa<UnaryOperator>(V))
    return hash(cast<Instruction>(V));

  return hashLeaf(V->getType());
}

ExpressionHasher::HashType ExpressionHasher::hash(Instruction *I) {
  if (InstHashes.count(I))
    return InstHashes[I];

  HashType H;
  unsigned NumOperands = I->getNumOperands();
  assert(NumOperands <= 3 && "instruction with unknown number of operands");
  auto Op = hashOpcode(I->getOpcode());
  if (NumOperands == 1) {
    H = hash_combine(Op, hashValue(I->getOperand(0)));
  } else if (NumOperands == 2) {
    H = hash_combine(Op, hashValue(I->getOperand(0)),
                     hashValue(I->getOperand(1)));
  } else if (NumOperands == 3) {
    H = hash_combine(Op, hashValue(I->getOperand(0)),
                     hashValue(I->getOperand(1)), hashValue(I->getOperand(2)));
  }
  return InstHashes[I] = H;
}
