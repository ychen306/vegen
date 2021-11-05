#ifndef IR_VEC_H
#define IR_VEC_H

// This file defines a pool of target-independent SIMD vector instructions
#include "InstSema.h"

namespace llvm {
class TargetTransformInfo;
} // namespace llvm

class BinaryIROperation : public Operation {
  const llvm::Instruction::BinaryOps Opcode;
  unsigned Bitwidth;

public:
  BinaryIROperation(decltype(Opcode) Opcode, unsigned Bitwidth)
      : Opcode(Opcode), Bitwidth(Bitwidth) {}
  std::string getName() const;
  unsigned getBitwidth() const { return Bitwidth; }
  llvm::Instruction::BinaryOps getOpcode() const { return Opcode; }
  bool match(llvm::Value *V,
             llvm::SmallVectorImpl<Match> &Matches) const override;
  unsigned getMaximumVF(llvm::TargetTransformInfo *) const;
};

// TODO: rename this to something like BinaryVectorBinding
class IRVectorBinding : public InstBinding {
  const BinaryIROperation *Op;

  IRVectorBinding(const BinaryIROperation *Op, std::string Name,
                  InstSignature Sig, std::vector<BoundOperation> LaneOps)
      : InstBinding(Name, {} /* no target features required*/, Sig, LaneOps),
        Op(Op) {}

public:
  static IRVectorBinding Create(const BinaryIROperation *Op,
                                unsigned VectorWidth);
  llvm::Value *emit(llvm::ArrayRef<llvm::Value *> Operands,
                    IntrinsicBuilder &Builder) const override;
  float getCost(llvm::TargetTransformInfo *TTI,
                llvm::LLVMContext &Ctx) const override;
  bool isSupported(llvm::TargetTransformInfo *) const;
};

struct Truncate : public Operation {
  unsigned InWidth, OutWidth;
  Truncate(unsigned InWidth, unsigned OutWidth)
      : InWidth(InWidth), OutWidth(OutWidth) {}
  bool match(llvm::Value *V,
             llvm::SmallVectorImpl<Match> &Matches) const override;
};

class VectorTruncate : public InstBinding {
  const Truncate *TruncOp;
  VectorTruncate(const Truncate *TruncOp, std::string Name, InstSignature Sig,
                 std::vector<BoundOperation> LaneOps)
      : InstBinding(Name, {} /* no target features required*/, Sig, LaneOps),
        TruncOp(TruncOp) {}

public:
  static VectorTruncate Create(const Truncate *TruncOp, unsigned VecLen);
  llvm::Value *emit(llvm::ArrayRef<llvm::Value *> Operands,
                    IntrinsicBuilder &Builder) const override;
  float getCost(llvm::TargetTransformInfo *TTI,
                llvm::LLVMContext &Ctx) const override;
};

struct Select : Operation {
  unsigned BitWidth;
  Select(unsigned BitWidth) : BitWidth(BitWidth) {}
  bool match(llvm::Value *V,
             llvm::SmallVectorImpl<Match> &Matches) const override;
};

class VectorSelect : public InstBinding {
  const Select *SelOp;
  VectorSelect(const Select *SelOp, std::string Name, InstSignature Sig,
               std::vector<BoundOperation> LaneOps)
      : InstBinding(Name, {} /* no target features required*/, Sig, LaneOps),
        SelOp(SelOp) {}

public:
  static VectorSelect Create(const Select *SelOp, unsigned VecLen);
  llvm::Value *emit(llvm::ArrayRef<llvm::Value *> Operands,
                    IntrinsicBuilder &Builder) const override;
  float getCost(llvm::TargetTransformInfo *TTI,
                llvm::LLVMContext &Ctx) const override;
};

struct UnaryMath : public Operation {
  llvm::Intrinsic::ID ID;
  bool IsDouble;

  UnaryMath(llvm::Intrinsic::ID ID, bool IsDouble) : ID(ID), IsDouble(IsDouble) {}
  bool match(llvm::Value *V,
             llvm::SmallVectorImpl<Match> &Matches) const override;
};

class VectorUnaryMath : public InstBinding {
  const UnaryMath *Op;
  VectorUnaryMath(const UnaryMath *Op, std::string Name, InstSignature Sig,
                  std::vector<BoundOperation> LaneOps)
      : InstBinding(Name, {} /* no target features required*/, Sig, LaneOps),
        Op(Op) {}

public:
  static VectorUnaryMath Create(const UnaryMath *Op, unsigned VecLen);
  llvm::Value *emit(llvm::ArrayRef<llvm::Value *> Operands,
                    IntrinsicBuilder &Builder) const override;
  float getCost(llvm::TargetTransformInfo *TTI,
                llvm::LLVMContext &Ctx) const override;
};

struct BinaryMath : public Operation {
  llvm::Intrinsic::ID ID;
  bool IsDouble;

  BinaryMath(llvm::Intrinsic::ID ID, bool IsDouble) : ID(ID), IsDouble(IsDouble) {}
  bool match(llvm::Value *V,
             llvm::SmallVectorImpl<Match> &Matches) const override;
};

class VectorBinaryMath : public InstBinding {
  const BinaryMath *Op;
  VectorBinaryMath(const BinaryMath *Op, std::string Name, InstSignature Sig,
                  std::vector<BoundOperation> LaneOps)
      : InstBinding(Name, {} /* no target features required*/, Sig, LaneOps),
        Op(Op) {}

public:
  static VectorBinaryMath Create(const BinaryMath *Op, unsigned VecLen);
  llvm::Value *emit(llvm::ArrayRef<llvm::Value *> Operands,
                    IntrinsicBuilder &Builder) const override;
  float getCost(llvm::TargetTransformInfo *TTI,
                llvm::LLVMContext &Ctx) const override;
};

// Aux class enumerating vector ir that we can emit
class IRInstTable {
  std::vector<BinaryIROperation> VectorizableOps;
  std::vector<IRVectorBinding> VectorInsts;

  std::vector<Truncate> TruncOps;
  std::vector<VectorTruncate> VectorTruncs;

  std::vector<Select> SelectOps;
  std::vector<VectorSelect> VectorSelects;

  std::vector<UnaryMath> UnaryMathOps;
  std::vector<VectorUnaryMath> VectorUnaryMathFuncs;

  std::vector<BinaryMath> BinaryMathOps;
  std::vector<VectorBinaryMath> VectorBinaryMathFuncs;

public:
  IRInstTable();
  // TODO: rename to get binary vector insts of something like that
  llvm::ArrayRef<IRVectorBinding> getBindings() const { return VectorInsts; }
  llvm::ArrayRef<VectorTruncate> getTruncates() const { return VectorTruncs; }
  llvm::ArrayRef<VectorSelect> getSelects() const { return VectorSelects; }
  llvm::ArrayRef<VectorUnaryMath> getUnaryMathFuncs() const { return VectorUnaryMathFuncs; }
  llvm::ArrayRef<VectorBinaryMath> getBinaryMathFuncs() const { return VectorBinaryMathFuncs; }
};

#endif // end IR_VEC_H
