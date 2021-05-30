#include "IRVec.h"
#include "llvm/Analysis/TargetTransformInfo.h"

using namespace llvm;

static bool isFloat(Instruction::BinaryOps Opcode) {
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

bool BinaryIROperation::match(Value *V, std::vector<Match> &Matches) const {
  auto *BinOp = dyn_cast<BinaryOperator>(V);
  bool Matched =
      BinOp && BinOp->getOpcode() == Opcode && hasBitWidth(BinOp, Bitwidth);
  if (Matched)
    Matches.push_back({// live ins of this operation
                       false,
                       {BinOp->getOperand(0), BinOp->getOperand(1)},
                       V});
  return Matched;
}

float IRVectorBinding::getCost(TargetTransformInfo *TTI,
                               LLVMContext &Ctx) const {
  Type *ScalarTy;
  unsigned ElemWidth = Op->getBitwidth();
  auto Opcode = Op->getOpcode();
  if (isFloat(Opcode)) {
    assert(ElemWidth == 32 || ElemWidth == 64);
    if (ElemWidth == 32)
      ScalarTy = Type::getFloatTy(Ctx);
    else
      ScalarTy = Type::getDoubleTy(Ctx);
  } else {
    ScalarTy = IntegerType::get(Ctx, ElemWidth);
  }
  unsigned NumElems = getLaneOps().size();
  auto *VecTy = FixedVectorType::get(ScalarTy, NumElems);
  return TTI->getArithmeticInstrCost(Opcode, VecTy);
}

IRVectorBinding IRVectorBinding::Create(const BinaryIROperation *Op,
                                        unsigned VectorWidth) {
  // Compute the signature of this BINARY vector inst
  InstSignature Sig = {// bitwidths of the inputs
                       {VectorWidth, VectorWidth},
                       // bitwidth of the output
                       {VectorWidth},
                       // has imm8?
                       false};

  unsigned ElemWidth = Op->getBitwidth();
  assert(VectorWidth % ElemWidth == 0);
  unsigned NumLanes = VectorWidth / ElemWidth;
  std::vector<BoundOperation> LaneOps;
  for (unsigned i = 0; i < NumLanes; i++) {
    unsigned Lo = i * ElemWidth, Hi = Lo + ElemWidth;
    LaneOps.push_back(BoundOperation(Op,
                                     // input binding
                                     {{0, Lo, Hi}, {1, Lo, Hi}}));
  }

  return IRVectorBinding(Op, Op->getName(), Sig, LaneOps);
}

Value *IRVectorBinding::emit(ArrayRef<Value *> Operands,
                             IntrinsicBuilder &Builder) const {
  assert(Operands.size() == 2);
  Instruction::BinaryOps Opcode = Op->getOpcode();
  return Builder.CreateBinOp(Opcode, Operands[0], Operands[1]);
}

IRInstTable::IRInstTable() {
  std::vector<Instruction::BinaryOps> VectorizableOpcodes = {
      Instruction::BinaryOps::Add,  Instruction::BinaryOps::FAdd,
      Instruction::BinaryOps::Sub,  Instruction::BinaryOps::FSub,
      Instruction::BinaryOps::Mul,  Instruction::BinaryOps::FMul,
      Instruction::BinaryOps::UDiv, Instruction::BinaryOps::SDiv,
      Instruction::BinaryOps::FDiv, Instruction::BinaryOps::URem,
      Instruction::BinaryOps::SRem, Instruction::BinaryOps::FRem,
      Instruction::BinaryOps::Shl,  Instruction::BinaryOps::LShr,
      Instruction::BinaryOps::AShr, Instruction::BinaryOps::And,
      Instruction::BinaryOps::Or,   Instruction::BinaryOps::Xor};

  // enumerate vectorizable scalar ops
  std::vector<unsigned> ScalarBitwidths = {8, 16, 32, 64};
  for (auto Opcode : VectorizableOpcodes)
    for (unsigned SB : ScalarBitwidths) {
      if (isFloat(Opcode) && SB != 32 && SB != 64)
        continue;
      VectorizableOps.emplace_back(Opcode, SB);
    }

  // enumerate vector insts
  std::vector<unsigned> VectorBitwidths = {64, 128, 256, 512};
  for (auto &Op : VectorizableOps) {
    for (unsigned VB : VectorBitwidths) {
      // Skip singleton pack
      if (VB / Op.getBitwidth() == 1)
        continue;
      VectorInsts.emplace_back(IRVectorBinding::Create(&Op, VB));
    }
  }

  for (auto &Binding : VectorInsts)
    Bindings.push_back(&Binding);
}
