#include "Preprocessing.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"

using namespace llvm;

OpcodeTable::OpcodeTable() {
  for (unsigned BW : Bitwidths)
    for (unsigned Opc : Opcodes) {
      // We reserve 3 values for unknown, cast and constant.
      unsigned TypeId = ValueTypeIds.size() + 3;
      ValueTypeIds[{Opc, BW}] = TypeId;
    }
}

unsigned OpcodeTable::getValueTypeId(Value *V) const {
  if (isa<ConstantInt>(V) || isa<ConstantFP>(V))
    return getConstId();
  if (auto *I = dyn_cast<Instruction>(V)) {
    if (I->isCast())
      return getCastId();
    llvm::Type *Ty;
    if (auto *SI = dyn_cast<StoreInst>(I))
      Ty = SI->getValueOperand()->getType();
    else
      Ty = I->getType();
    auto It = ValueTypeIds.find({I->getOpcode(), getBitwidth(Ty)});
    if (It != ValueTypeIds.end())
      return It->second;
  }
  return getUnknownTypeId();
}

std::vector<unsigned> OpcodeTable::Bitwidths = {8, 16, 32, 64};
// TODO: support PHI
std::vector<unsigned> OpcodeTable::Opcodes = {
    /*Instruction::PHI, */ Instruction::Load,
    Instruction::Store,
    Instruction::Add,
    Instruction::FAdd,
    Instruction::Sub,
    Instruction::FSub,
    Instruction::Mul,
    Instruction::FMul,
    Instruction::UDiv,
    Instruction::SDiv,
    Instruction::FDiv,
    Instruction::URem,
    Instruction::SRem,
    Instruction::FRem,
    Instruction::Shl,
    Instruction::LShr,
    Instruction::AShr,
    Instruction::And,
    Instruction::Or,
    Instruction::Xor};

void IRIndex::trackValue(Value *V) {
  if (Value2IdMap.count(V))
    return;
  unsigned Id = Values.size();
  Values.push_back(V);
  Value2IdMap[V] = Id;
}

IRIndex::IRIndex(const Frontier *Frt) : Frt(Frt) {
  BasicBlock *BB = Frt->getBasicBlock();
  for (auto &I : *BB) {
    if (!Frt->isFree(&I))
      continue;
    trackValue(&I);
    for (Value *Operand : I.operands())
      trackValue(Operand);
  }
}

bool IRIndex::isFree(unsigned i) const {
  auto *I = dyn_cast<Instruction>(get(i));
  if (I)
    return I->getParent() == Frt->getBasicBlock() && Frt->isFree(I);
  return true;
}

std::vector<int64_t> getValueTypes(ArrayRef<IRIndex> Indexes) {
  std::vector<int64_t> ValueTypes;
  for (auto &Index : Indexes) {
    unsigned N = Index.getNumValues();
    for (unsigned i = 0; i < N; i++) {
      unsigned TypeId;
      if (Index.isFree(i))
        TypeId = OpTable.getValueTypeId(Index.get(i));
      else
        TypeId = OpTable.getUnknownTypeId();
      ValueTypes.push_back(TypeId);
    }
  }
  return ValueTypes;
}

OpcodeTable OpTable;
