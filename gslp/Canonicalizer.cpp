#include "Canonicalizer.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"

using namespace llvm;

Canonicalizer::Node *Canonicalizer::getOrCreate(NodeSignature Sig) {
  auto &Slot = Nodes[Sig];
  if (!Slot)
    Slot.reset(new Node());
  return Slot.get();
}

Canonicalizer::Node *Canonicalizer::getNodeForValue(Value *V) {
  if (isa<BinaryOperator>(V) || isa<SelectInst>(V) ||
      isa<CastInst>(V) || isa<CmpInst>(V) || isa<UnaryOperator>(V))
    return get(cast<Instruction>(V));

  return getOrCreate(NodeSignature(V->getType(), ~0u, nullptr, nullptr, nullptr));
}

Canonicalizer::Node *Canonicalizer::get(Instruction *I) {
  unsigned NumOperands = I->getNumOperands();
  assert(NumOperands <= 3 && "instruction with unknown number of operands");

  Node *Arg1 = nullptr;
  Node *Arg2 = nullptr;
  Node *Arg3 = nullptr;
  if (NumOperands >= 1) {
    Arg1 = getNodeForValue(I->getOperand(0));
  } else if (NumOperands >= 2) {
    Arg2 = getNodeForValue(I->getOperand(1));
  } else if (NumOperands == 3) {
    Arg3 = getNodeForValue(I->getOperand(2));
  }
  Node *N = getOrCreate(NodeSignature(I->getType(), I->getOpcode(), Arg1, Arg2, Arg3));
  N->Members.insert(I);
  return N;
}
