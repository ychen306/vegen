#ifndef IR_VEC_H
#define IR_VEC_H

// This file defines a pool of target-independent SIMD vector instructions
#include "InstSema.h"

namespace llvm {
class TargetTransformInfo;
}

class BinaryIROperation : public Operation {
  const llvm::Instruction::BinaryOps Opcode;
  unsigned Bitwidth;

public:
  BinaryIROperation(decltype(Opcode) Opcode, unsigned Bitwidth)
      : Opcode(Opcode), Bitwidth(Bitwidth) {}
  std::string getName() const {
    return llvm::Instruction::getOpcodeName(Opcode);
  }
  unsigned getBitwidth() const { return Bitwidth; }
  llvm::Instruction::BinaryOps getOpcode() const { return Opcode; }
  bool match(llvm::Value *V, llvm::SmallVectorImpl<Match> &Matches) const override;
  unsigned getMaximumVF(llvm::TargetTransformInfo *) const;
};

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

// Aux class enumerating vector ir that we can emit
class IRInstTable {
  std::vector<BinaryIROperation> VectorizableOps;
  std::vector<IRVectorBinding> VectorInsts;

public:
  IRInstTable();
  llvm::ArrayRef<IRVectorBinding> getBindings() const { return VectorInsts; }
};

#endif // end IR_VEC_H
