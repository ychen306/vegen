#include "Canonicalizer.h"
#include "llvm/ADT/Hashing.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"

using namespace llvm;

Canonicalizer::HashType Canonicalizer::hashLeaf(Type *Ty) {
  if (LeafHashes.count(Ty))
    return LeafHashes[Ty];
  return LeafHashes[Ty] = (*RNG)();
}

Canonicalizer::HashType Canonicalizer::hashOpcode(unsigned Opcode) {
  if (OpcodeHashes.count(Opcode))
    return OpcodeHashes[Opcode];
  return OpcodeHashes[Opcode] = (*RNG)();
}

Canonicalizer::Node *Canonicalizer::canonicalize(const Node &N) {
  auto &Slot = Nodes[N];
  if (!Slot)
    Slot.reset(new Node(N));
  return Slot.get();
}

Canonicalizer::Node *Canonicalizer::getNodeForValue(Value *V) {
  if (isa<BinaryOperator>(V) || isa<SelectInst>(V) ||
      isa<CastInst>(V) || isa<CmpInst>(V) || isa<UnaryOperator>(V))
    return get(cast<Instruction>(V));

  Node N(V->getType());
  N.Hash = hashLeaf(V->getType());
  return canonicalize(N);
}

Canonicalizer::Node *Canonicalizer::get(Instruction *I) {
  unsigned NumOperands = I->getNumOperands();
  assert(NumOperands <= 3 && "instruction with unknown number of operands");

  auto OpHash = hashOpcode(I->getOpcode());

  HashType Hash;
  Node N(I->getType());
  N.Opcode = I->getOpcode();
  if (NumOperands == 1) {
    N.Arg1 = getNodeForValue(I->getOperand(0));
    N.Hash = hash_combine(OpHash, N.Arg1->Hash);
  } else if (NumOperands == 2) {
    N.Arg1 = getNodeForValue(I->getOperand(0));
    N.Arg2 = getNodeForValue(I->getOperand(1));
    N.Hash = hash_combine(OpHash, N.Arg1->Hash, N.Arg2->Hash);
  } else if (NumOperands == 3) {
    N.Arg1 = getNodeForValue(I->getOperand(0));
    N.Arg2 = getNodeForValue(I->getOperand(1));
    N.Arg3 = getNodeForValue(I->getOperand(2));
    N.Hash = hash_combine(OpHash, N.Arg1->Hash, N.Arg2->Hash, N.Arg3->Hash);
  }

  Node *Canonical = canonicalize(N);
  Canonical->Members.insert(I);
  return Canonical;
}
