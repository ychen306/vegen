#include "IRVec.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/Support/FormatVariadic.h"

using namespace llvm;
using namespace PatternMatch;

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

bool BinaryIROperation::match(Value *V, SmallVectorImpl<Match> &Matches) const {
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

unsigned BinaryIROperation::getMaximumVF(TargetTransformInfo *TTI) const {
  return TTI->getLoadStoreVecRegBitWidth(0) / Bitwidth;
}

bool IRVectorBinding::isSupported(TargetTransformInfo *TTI) const {
  return getLaneOps().size() <= Op->getMaximumVF(TTI);
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
  std::vector<unsigned> ScalarBitwidths = {1, 8, 16, 32, 64};
  for (auto Opcode : VectorizableOpcodes)
    for (unsigned SB : ScalarBitwidths) {
      if (isFloat(Opcode) && SB != 32 && SB != 64)
        continue;
      VectorizableOps.emplace_back(Opcode, SB);
    }

  // enumerate vector insts
  std::vector<unsigned> VectorBitwidths = {64, 128, 256, 512};
  for (auto &Op : VectorizableOps) {
    if (Op.getBitwidth() == 1)
      continue;
    for (unsigned VB : VectorBitwidths) {
      // Skip singleton pack
      if (VB / Op.getBitwidth() == 1)
        continue;
      VectorInsts.push_back(IRVectorBinding::Create(&Op, VB));
    }
  }

  // Special case for boolean ops
  for (auto &Op : VectorizableOps) {
    if (Op.getBitwidth() != 1)
      continue;
    for (unsigned VL : {2, 4, 8, 16})
      VectorInsts.push_back(IRVectorBinding::Create(&Op, VL));
  }

  for (unsigned InWidth : ScalarBitwidths)
    for (unsigned OutWidth : ScalarBitwidths)
      if (InWidth > OutWidth)
        TruncOps.emplace_back(InWidth, OutWidth);

  for (unsigned BitWidth : ScalarBitwidths)
    SelectOps.emplace_back(BitWidth);

  for (unsigned VL : {2, 4, 8, 16}) {
    for (auto &TruncOp : TruncOps)
      VectorTruncs.push_back(VectorTruncate::Create(&TruncOp, VL));
    for (auto &SelOp : SelectOps)
      VectorSelects.push_back(VectorSelect::Create(&SelOp, VL));
  }

}

bool Truncate::match(Value *V, SmallVectorImpl<Match> &Matches) const {
  Value *X;
  if (PatternMatch::match(V, m_Trunc(m_Value(X))) && hasBitWidth(X, InWidth) &&
      hasBitWidth(V, OutWidth)) {

    Matches.push_back({false, {X}, V});
    return true;
  }
  return false;
}

VectorTruncate VectorTruncate::Create(const Truncate *TruncOp,
                                      unsigned VecLen) {
  unsigned InWidth = TruncOp->InWidth, OutWidth = TruncOp->OutWidth;
  InstSignature Sig = {// bitwidths of the inputs
                       {InWidth * VecLen},
                       // bitwidth of the output
                       {OutWidth * VecLen},
                       // has imm8?
                       false};

  std::vector<BoundOperation> LaneOps;
  for (unsigned i = 0; i < VecLen; i++) {
    unsigned Lo = i * InWidth, Hi = Lo + InWidth;
    LaneOps.push_back(BoundOperation(TruncOp, {{0, Lo, Hi}}));
  }
  std::string Name = formatv("trunc-i{0}-to-i{1}", InWidth, OutWidth).str();
  return VectorTruncate(TruncOp, Name, Sig, LaneOps);
}

Value *VectorTruncate::emit(ArrayRef<Value *> Operands,
                            IntrinsicBuilder &Builder) const {
  assert(Operands.size() == 1);
  auto &Ctx = Builder.getContext();
  unsigned VL = getLaneOps().size();
  auto *OutTy =
      FixedVectorType::get(Type::getIntNTy(Ctx, TruncOp->OutWidth), VL);
  return Builder.CreateTrunc(Operands.front(), OutTy);
}

float VectorTruncate::getCost(TargetTransformInfo *TTI,
                              LLVMContext &Ctx) const {
  unsigned VL = getLaneOps().size();
  auto *InTy = FixedVectorType::get(Type::getIntNTy(Ctx, TruncOp->InWidth), VL);
  auto *OutTy =
      FixedVectorType::get(Type::getIntNTy(Ctx, TruncOp->OutWidth), VL);
  return TTI->getCastInstrCost(Instruction::CastOps::Trunc, OutTy, InTy,
                               TTI::CastContextHint::None,
                               TTI::TCK_RecipThroughput);
}

bool Select::match(Value *V, SmallVectorImpl<Match> &Matches) const {
  Value *Cond, *X, *Y;
  if (PatternMatch::match(V, m_Select(m_Value(Cond), m_Value(X), m_Value(Y))) &&
      hasBitWidth(X, BitWidth) && hasBitWidth(Y, BitWidth)) {
    Matches.push_back({false, {Cond, X, Y}, V});
    return true;
  }
  return false;
}

VectorSelect VectorSelect::Create(const Select *SelOp, unsigned VecLen) {
  unsigned BitWidth = SelOp->BitWidth;
  InstSignature Sig = {// bitwidths of the inputs
                       {1 * VecLen, BitWidth * VecLen, BitWidth * VecLen},
                       // bitwidth of the output
                       {BitWidth * VecLen},
                       // has imm8?
                       false};

  std::vector<BoundOperation> LaneOps;
  for (unsigned i = 0; i < VecLen; i++) {
    unsigned Lo = i * BitWidth, Hi = Lo + BitWidth;
    LaneOps.push_back(BoundOperation(SelOp, 
          {
            {0,i, i+1}, {1, Lo, Hi}, {2, Lo, Hi},
          }));
  }
  std::string Name = formatv("select-i{0}", BitWidth).str();
  return VectorSelect(SelOp, Name, Sig, LaneOps);
}

Value *VectorSelect::emit(ArrayRef<Value *> Operands,
                          IntrinsicBuilder &Builder) const {
  assert(Operands.size() == 3);
  auto *Cond = Operands[0], *X = Operands[1], *Y = Operands[2];
  if (Y->getType() != X->getType())
    Y = Builder.CreateBitCast(Y, X->getType());
  return Builder.CreateSelect(Cond, X, Y);
}

float VectorSelect::getCost(TargetTransformInfo *TTI, LLVMContext &Ctx) const {
  unsigned VL = getLaneOps().size();
  auto *VecTy = FixedVectorType::get(Type::getIntNTy(Ctx, SelOp->BitWidth), VL);
  return TTI->getArithmeticInstrCost(Instruction::Select, VecTy);
}
