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

bool UnaryIROperation::match(Value *V, SmallVectorImpl<Match> &Matches) const {
  auto *I = dyn_cast<Instruction>(V);
  if (!I || I->getOpcode() != Opcode || !hasBitWidth(V, Bitwidth))
    return false;
  Matches.push_back({false, {I->getOperand(0)}, V});
  return true;
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

float UnaryIRVectorBinding::getCost(TargetTransformInfo *TTI,
                                    LLVMContext &Ctx) const {
  unsigned ElemWidth = Op->getBitwidth();
  auto Opcode = Op->getOpcode();
  unsigned NumElems = getLaneOps().size();

  if (Opcode == Instruction::FNeg) {
    auto *Ty = ElemWidth == 32 ? Type::getFloatTy(Ctx) : Type::getDoubleTy(Ctx);
    auto *VecTy = FixedVectorType::get(Ty, NumElems);
    return TTI->getArithmeticInstrCost(Opcode, VecTy);
  }

  return 1.0;

  Type *InTy, *OutTy;
  if (Opcode == Instruction::SIToFP) {
    InTy = Type::getIntNTy(Ctx, ElemWidth);
    OutTy = ElemWidth == 32 ? Type::getFloatTy(Ctx) : Type::getDoubleTy(Ctx);
  } else if (Opcode == Instruction::FPToSI) {
    InTy = ElemWidth == 32 ? Type::getFloatTy(Ctx) : Type::getDoubleTy(Ctx);
    OutTy = Type::getIntNTy(Ctx, ElemWidth);
  } else {
    llvm_unreachable("unsupport unary opcode");
  }

  return TTI->getCastInstrCost(Opcode, FixedVectorType::get(InTy, NumElems),
                               FixedVectorType::get(OutTy, NumElems),
                               TTI::CastContextHint::None,
                               TTI::TCK_RecipThroughput);
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

UnaryIRVectorBinding UnaryIRVectorBinding::Create(const UnaryIROperation *Op,
                                                  unsigned VectorWidth) {
  // Compute the signature of this UNARY vector inst
  InstSignature Sig = {// bitwidths of the inputs
                       {VectorWidth},
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
                                     {{0, Lo, Hi}}));
  }

  return UnaryIRVectorBinding(Op, Op->getName(), Sig, LaneOps);
}

Value *IRVectorBinding::emit(ArrayRef<Value *> Operands,
                             IntrinsicBuilder &Builder) const {
  assert(Operands.size() == 2);
  Instruction::BinaryOps Opcode = Op->getOpcode();
  return Builder.CreateBinOp(Opcode, Operands[0], Operands[1]);
}

static Value *tryCast(IRBuilderBase &Builder, Value *V, Type *Ty) {
  if (V->getType() == Ty)
    return V;
  return Builder.CreateBitCast(V, Ty);
}

Value *UnaryIRVectorBinding::emit(ArrayRef<Value *> Operands,
                                  IntrinsicBuilder &Builder) const {
  assert(Operands.size() == 1);
  unsigned ElemWidth = Op->getBitwidth();
  unsigned VecLen = getLaneOps().size();
  auto &Ctx = Builder.getContext();
  auto *FloatTy =
    FixedVectorType::get(
      ElemWidth == 32 ? Type::getFloatTy(Ctx) : Type::getDoubleTy(Ctx), VecLen);
  auto *IntTy = FixedVectorType::get(Type::getIntNTy(Ctx, ElemWidth), VecLen);
  auto *V = Operands.front();
  switch (Op->getOpcode()) {
  case Instruction::SIToFP:
    return Builder.CreateSIToFP(tryCast(Builder, V, IntTy), FloatTy);
  case Instruction::FPToSI:
    return Builder.CreateFPToSI(tryCast(Builder, V, FloatTy), IntTy);
  case Instruction::FNeg:
    return Builder.CreateFNeg(tryCast(Builder, V, FloatTy));
  default:
    llvm_unreachable("unsupport unary opcode");
  }
}

unsigned BinaryIROperation::getMaximumVF(TargetTransformInfo *TTI) const {
  return TTI->getLoadStoreVecRegBitWidth(0) / Bitwidth;
}

unsigned UnaryIROperation::getMaximumVF(TargetTransformInfo *TTI) const {
  return TTI->getLoadStoreVecRegBitWidth(0) / Bitwidth;
}

std::string BinaryIROperation::getName() const {
  return formatv("{0}-i{1}", Instruction::getOpcodeName(Opcode), Bitwidth)
      .str();
}

std::string UnaryIROperation::getName() const {
  return formatv("{0}-{1}", Instruction::getOpcodeName(Opcode), Bitwidth).str();
}

bool IRVectorBinding::isSupported(TargetTransformInfo *TTI) const {
  return getLaneOps().size() <= Op->getMaximumVF(TTI);
}

bool UnaryIRVectorBinding::isSupported(TargetTransformInfo *TTI) const {
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

  std::vector<unsigned> UnaryOpcodes = {Instruction::FNeg};
  for (unsigned Opcode : UnaryOpcodes) {
    for (unsigned SB : {32, 64}) {
      UnaryOps.emplace_back(Opcode, SB);
    }
  }

  // sitofp and fptosi
  for (unsigned SB : ScalarBitwidths) {
    FloatToIntOps.emplace_back(SB, true);
    FloatToIntOps.emplace_back(SB, false);
    IntToFloatOps.emplace_back(SB, true);
    IntToFloatOps.emplace_back(SB, false);
  }

  for (unsigned VL : {2,4,8,16}) {
    for (auto &Op : FloatToIntOps)
      VectorFloatToInts.push_back(VectorFloatToInt::Create(&Op, VL));
    for (auto &Op : IntToFloatOps)
      VectorIntToFloats.push_back(VectorIntToFloat::Create(&Op, VL));
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
  for (auto &Op : UnaryOps) {
    for (unsigned VB : VectorBitwidths) {
      // Skip singleton pack
      if (VB / Op.getBitwidth() == 1)
        continue;
      UnaryVectorInsts.push_back(UnaryIRVectorBinding::Create(&Op, VB));
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
    for (unsigned OutWidth : ScalarBitwidths) {
      if (InWidth > OutWidth)
        TruncOps.emplace_back(InWidth, OutWidth);
      else if (InWidth < OutWidth) {
        ExtOps.emplace_back(InWidth, OutWidth, true);
        ExtOps.emplace_back(InWidth, OutWidth, false);
      }
    }

  for (unsigned BitWidth : ScalarBitwidths)
    SelectOps.emplace_back(BitWidth);

  Intrinsic::ID FPUnaryIntrins[] = {
      Intrinsic::sin,  Intrinsic::cos,  Intrinsic::exp,
      Intrinsic::exp2, Intrinsic::log,  Intrinsic::log10,
      Intrinsic::log2, Intrinsic::fabs, Intrinsic::sqrt,
  };
  for (auto ID : FPUnaryIntrins) {
    UnaryMathOps.emplace_back(ID, 32, true);
    UnaryMathOps.emplace_back(ID, 64, true);
  }
  Intrinsic::ID IntUnaryIntrins[] = { Intrinsic::abs, };
  for (unsigned BitWidth : ScalarBitwidths)
    for (auto ID : IntUnaryIntrins)
        UnaryMathOps.emplace_back(ID, BitWidth, false);

  BinaryMathOps.emplace_back(Intrinsic::pow, true);
  BinaryMathOps.emplace_back(Intrinsic::pow, false);

  for (unsigned VL : {2, 4, 8, 16}) {
    for (auto &TruncOp : TruncOps)
      VectorTruncs.push_back(VectorTruncate::Create(&TruncOp, VL));
    for (auto &ExtOp : ExtOps)
      VectorExtensions.push_back(VectorExtension::Create(&ExtOp, VL));
    for (auto &SelOp : SelectOps)
      VectorSelects.push_back(VectorSelect::Create(&SelOp, VL));
    for (auto &UnaryOp : UnaryMathOps)
      VectorUnaryMathFuncs.push_back(VectorUnaryMath::Create(&UnaryOp, VL));
    for (auto &BinaryOp : BinaryMathOps)
      VectorBinaryMathFuncs.push_back(VectorBinaryMath::Create(&BinaryOp, VL));
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

/////
bool FloatToInt::match(Value *V, SmallVectorImpl<Match> &Matches) const {
  Value *X;
  if (PatternMatch::match(V, m_FPToSI(m_Value(X))) && hasBitWidth(X, IsFloat ? 32 : 64) &&
      hasBitWidth(V, OutWidth)) {
    Matches.push_back({false, {X}, V});
    return true;
  }
  return false;
}

bool IntToFloat::match(Value *V, SmallVectorImpl<Match> &Matches) const {
  Value *X;
  if (PatternMatch::match(V, m_SIToFP(m_Value(X))) && hasBitWidth(X, InWidth) &&
      hasBitWidth(V, IsFloat ? 32 : 64)) {
    Matches.push_back({false, {X}, V});
    return true;
  }
  return false;
}

VectorFloatToInt VectorFloatToInt::Create(const FloatToInt *Op,
                                      unsigned VecLen) {
  unsigned InWidth = Op->IsFloat ? 32 : 64, OutWidth = Op->OutWidth;
  InstSignature Sig = {// bitwidths of the inputs
                       {InWidth * VecLen},
                       // bitwidth of the output
                       {OutWidth * VecLen},
                       // has imm8?
                       false};

  std::vector<BoundOperation> LaneOps;
  for (unsigned i = 0; i < VecLen; i++) {
    unsigned Lo = i * InWidth, Hi = Lo + InWidth;
    LaneOps.push_back(BoundOperation(Op, {{0, Lo, Hi}}));
  }
  std::string Name = formatv("fptosi-i{0}-to-f{1}", InWidth, OutWidth).str();
  return VectorFloatToInt(Op, Name, Sig, LaneOps);
}

VectorIntToFloat VectorIntToFloat::Create(const IntToFloat *Op,
                                      unsigned VecLen) {
  unsigned InWidth = Op->InWidth, OutWidth = Op->IsFloat ? 32 : 64;
  InstSignature Sig = {// bitwidths of the inputs
                       {InWidth * VecLen},
                       // bitwidth of the output
                       {OutWidth * VecLen},
                       // has imm8?
                       false};

  std::vector<BoundOperation> LaneOps;
  for (unsigned i = 0; i < VecLen; i++) {
    unsigned Lo = i * InWidth, Hi = Lo + InWidth;
    LaneOps.push_back(BoundOperation(Op, {{0, Lo, Hi}}));
  }
  std::string Name = formatv("sitofp-i{0}-to-f{1}", InWidth, OutWidth).str();
  return VectorIntToFloat(Op, Name, Sig, LaneOps);
}

Value *VectorFloatToInt::emit(ArrayRef<Value *> Operands,
                            IntrinsicBuilder &Builder) const {
  assert(Operands.size() == 1);
  auto &Ctx = Builder.getContext();
  unsigned VL = getLaneOps().size();
  auto *OutTy =
      FixedVectorType::get(Type::getIntNTy(Ctx, Op->OutWidth), VL);
  return Builder.CreateFPToSI(Operands.front(), OutTy);
}

Value *VectorIntToFloat::emit(ArrayRef<Value *> Operands,
                            IntrinsicBuilder &Builder) const {
  assert(Operands.size() == 1);
  auto &Ctx = Builder.getContext();
  unsigned VL = getLaneOps().size();
  auto *OutTy =
      FixedVectorType::get(Op->IsFloat ? Type::getFloatTy(Ctx) : Type::getDoubleTy(Ctx), VL);
  return Builder.CreateSIToFP(Operands.front(), OutTy);
}

float VectorFloatToInt::getCost(TargetTransformInfo *TTI,
                              LLVMContext &Ctx) const {
  unsigned VL = getLaneOps().size();
  auto *InTy = FixedVectorType::get(Op->IsFloat ? Type::getFloatTy(Ctx) : Type::getDoubleTy(Ctx), VL);
  auto *OutTy =
      FixedVectorType::get(Type::getIntNTy(Ctx, Op->OutWidth), VL);
  return TTI->getCastInstrCost(Instruction::CastOps::FPToSI, OutTy, InTy,
                               TTI::CastContextHint::None,
                               TTI::TCK_RecipThroughput);
}

float VectorIntToFloat::getCost(TargetTransformInfo *TTI,
                              LLVMContext &Ctx) const {
  unsigned VL = getLaneOps().size();
  auto *InTy =
      FixedVectorType::get(Type::getIntNTy(Ctx, Op->InWidth), VL);
  auto *OutTy = FixedVectorType::get(Op->IsFloat ? Type::getFloatTy(Ctx) : Type::getDoubleTy(Ctx), VL);
  return TTI->getCastInstrCost(Instruction::CastOps::SIToFP, OutTy, InTy,
                               TTI::CastContextHint::None,
                               TTI::TCK_RecipThroughput);
}

bool Extension::match(Value *V, SmallVectorImpl<Match> &Matches) const {
  Value *X;
  bool Matched = 
    (Signed && PatternMatch::match(V, m_SExt(m_Value(X)))) ||
    (!Signed && PatternMatch::match(V, m_ZExt(m_Value(X))));
  if (Matched && hasBitWidth(X, InWidth) &&
      hasBitWidth(V, OutWidth)) {
    Matches.push_back({false, {X}, V});
    return true;
  }
  return false;
}

VectorExtension VectorExtension::Create(const Extension *ExtOp,
                                      unsigned VecLen) {
  unsigned InWidth = ExtOp->InWidth, OutWidth = ExtOp->OutWidth;
  InstSignature Sig = {// bitwidths of the inputs
                       {InWidth * VecLen},
                       // bitwidth of the output
                       {OutWidth * VecLen},
                       // has imm8?
                       false};

  std::vector<BoundOperation> LaneOps;
  for (unsigned i = 0; i < VecLen; i++) {
    unsigned Lo = i * InWidth, Hi = Lo + InWidth;
    LaneOps.push_back(BoundOperation(ExtOp, {{0, Lo, Hi}}));
  }
  std::string Name = formatv("{0}ext-i{1}-to-i{2}", ExtOp->Signed ? 's' : 'z', InWidth, OutWidth).str();
  return VectorExtension(ExtOp, Name, Sig, LaneOps);
}

Value *VectorExtension::emit(ArrayRef<Value *> Operands,
                            IntrinsicBuilder &Builder) const {
  assert(Operands.size() == 1);
  auto &Ctx = Builder.getContext();
  unsigned VL = getLaneOps().size();
  auto *OutTy =
      FixedVectorType::get(Type::getIntNTy(Ctx, ExtOp->OutWidth), VL);
  if (ExtOp->Signed)
    return Builder.CreateSExt(Operands.front(), OutTy);
  return Builder.CreateZExt(Operands.front(), OutTy);
}

float VectorExtension::getCost(TargetTransformInfo *TTI,
                              LLVMContext &Ctx) const {
  unsigned VL = getLaneOps().size();
  auto *InTy = FixedVectorType::get(Type::getIntNTy(Ctx, ExtOp->InWidth), VL);
  auto *OutTy =
      FixedVectorType::get(Type::getIntNTy(Ctx, ExtOp->OutWidth), VL);
  auto Op = ExtOp->Signed ? Instruction::CastOps::SExt : Instruction::CastOps::ZExt;
  return TTI->getCastInstrCost(Op, OutTy, InTy,
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
    LaneOps.push_back(BoundOperation(SelOp, {
                                                {0, i, i + 1},
                                                {1, Lo, Hi},
                                                {2, Lo, Hi},
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

bool UnaryMath::match(Value *V, SmallVectorImpl<Match> &Matches) const {
  // Match for the right floating type
  auto &Ctx = V->getContext();
  if (!hasBitWidth(V, BitWidth))
    return false;

  // Match the intrinsic call
  auto *Call = dyn_cast<CallInst>(V);
  if (!Call || !Call->getCalledFunction() ||
      Call->getCalledFunction()->getIntrinsicID() != ID)
    return false;

  assert(Call->arg_size() == 1 || ID == Intrinsic::abs);
  Matches.push_back({false, {Call->getArgOperand(0)}, V});
  return true;
}

VectorUnaryMath VectorUnaryMath::Create(const UnaryMath *Op, unsigned VecLen) {
  unsigned BitWidth = Op->BitWidth;
  InstSignature Sig = {// bitwidths of the inputs
                       {BitWidth * VecLen},
                       // bitwidth of the output
                       {BitWidth * VecLen},
                       // has imm8?
                       false};

  std::vector<BoundOperation> LaneOps;
  for (unsigned i = 0; i < VecLen; i++) {
    unsigned Lo = i * BitWidth, Hi = Lo + BitWidth;
    LaneOps.push_back(BoundOperation(Op, {{0, Lo, Hi}}));
  }

  std::string Name = formatv("{0}-x-{1}", "builtin-math",
                             BitWidth, VecLen)
                         .str();
  return VectorUnaryMath(Op, Name, Sig, LaneOps);
}

static Type *getType(LLVMContext &Ctx, unsigned BitWidth, bool IsFloat) {
  if (IsFloat) {
    assert(BitWidth == 32 || BitWidth == 64);
    return BitWidth == 32 ? Type::getFloatTy(Ctx) : Type::getDoubleTy(Ctx);
  }
  return Type::getIntNTy(Ctx, BitWidth);
}

Value *VectorUnaryMath::emit(ArrayRef<Value *> Operands,
                             IntrinsicBuilder &Builder) const {
  auto *M = Builder.GetInsertBlock()->getModule();
  auto &Ctx = Builder.getContext();
  Type *Ty = getType(Ctx, Op->BitWidth, Op->IsFloat);
  unsigned VecLen = getLaneOps().size();
  auto *F =
      Intrinsic::getDeclaration(M, Op->ID, {FixedVectorType::get(Ty, VecLen)});
  assert(Operands.size() == 1);
  if (Op->ID == Intrinsic::abs)
    return Builder.CreateCall(F, {Operands.front(), Builder.getTrue()/*is int min poison*/});
  return Builder.CreateCall(F, {Operands.front()});
}

float VectorUnaryMath::getCost(TargetTransformInfo *TTI,
                               LLVMContext &Ctx) const {
  auto *Ty = getType(Ctx, Op->BitWidth, Op->IsFloat);
  unsigned VecLen = getLaneOps().size();
  auto *VecTy = FixedVectorType::get(Ty, VecLen);
  return TTI->getIntrinsicInstrCost(
      IntrinsicCostAttributes(Op->ID, VecTy, {VecTy}),
      TTI::TCK_RecipThroughput);
}

bool BinaryMath::match(Value *V, SmallVectorImpl<Match> &Matches) const {
  // Match for the right floating type
  auto &Ctx = V->getContext();
  if (IsDouble && V->getType() != Type::getDoubleTy(Ctx))
    return false;
  bool IsFloat = !IsDouble;
  if (IsFloat && V->getType() != Type::getFloatTy(Ctx))
    return false;

  // Match the intrinsic call
  auto *Call = dyn_cast<CallInst>(V);
  if (!Call || !Call->getCalledFunction() ||
      Call->getCalledFunction()->getIntrinsicID() != ID)
    return false;

  assert(Call->arg_size() == 2);
  Matches.push_back(
      {false, {Call->getArgOperand(0), Call->getArgOperand(1)}, V});
  return true;
}

VectorBinaryMath VectorBinaryMath::Create(const BinaryMath *Op,
                                          unsigned VecLen) {
  unsigned BitWidth = Op->IsDouble ? 64 : 32;
  unsigned VectorWidth = BitWidth * VecLen;
  InstSignature Sig = {// bitwidths of the inputs
                       {VectorWidth, VectorWidth},
                       // bitwidth of the output
                       {VectorWidth},
                       // has imm8?
                       false};

  std::vector<BoundOperation> LaneOps;
  for (unsigned i = 0; i < VecLen; i++) {
    unsigned Lo = i * BitWidth, Hi = Lo + BitWidth;
    LaneOps.push_back(BoundOperation(Op, {{0, Lo, Hi}, {1, Lo, Hi}}));
  }

  std::string Name = formatv("{0}-x-{1}", "builtin-math",
                             Op->IsDouble ? "double" : "float", VecLen)
                         .str();
  return VectorBinaryMath(Op, Name, Sig, LaneOps);
}

Value *VectorBinaryMath::emit(ArrayRef<Value *> Operands,
                              IntrinsicBuilder &Builder) const {
  auto *M = Builder.GetInsertBlock()->getModule();
  auto &Ctx = Builder.getContext();
  auto *Ty = Op->IsDouble ? Type::getDoubleTy(Ctx) : Type::getFloatTy(Ctx);
  unsigned VecLen = getLaneOps().size();
  auto *F =
      Intrinsic::getDeclaration(M, Op->ID, {FixedVectorType::get(Ty, VecLen)});
  assert(Operands.size() == 2);
  return Builder.CreateCall(F, {Operands[0], Operands[1]});
}

float VectorBinaryMath::getCost(TargetTransformInfo *TTI,
                                LLVMContext &Ctx) const {
  auto *Ty = Op->IsDouble ? Type::getDoubleTy(Ctx) : Type::getFloatTy(Ctx);
  unsigned VecLen = getLaneOps().size();
  auto *VecTy = FixedVectorType::get(Ty, VecLen);
  return TTI->getIntrinsicInstrCost(
      IntrinsicCostAttributes(Op->ID, VecTy, {VecTy, VecTy}),
      TTI::TCK_RecipThroughput);
}
