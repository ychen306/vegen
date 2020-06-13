#ifndef IR_VEC_H
#define IR_VEC_H

#include "InstSema.h"
#include "Util.h"
#include "llvm/Analysis/TargetTransformInfo.h"

using namespace llvm;

class BinaryIROperation : public Operation {
  const Instruction::BinaryOps Opcode;
  unsigned Bitwidth;

public:
  BinaryIROperation(Instruction::BinaryOps Opcode, unsigned Bitwidth)
      : Opcode(Opcode), Bitwidth(Bitwidth) {}
  std::string getName() const { return Instruction::getOpcodeName(Opcode); }
  unsigned getBitwidth() const { return Bitwidth; }
  Instruction::BinaryOps getOpcode() const { return Opcode; }
  bool match(llvm::Value *V, std::vector<Match> &Matches) const override {
    auto *BinOp = dyn_cast<BinaryOperator>(V);
    bool Matched =
        BinOp && BinOp->getOpcode() == Opcode && hasBitWidth(BinOp, Bitwidth);
    if (Matched)
      Matches.push_back({// live ins of this operation
                         {BinOp->getOperand(0), BinOp->getOperand(1)},
                         V});
    return Matched;
  }
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
  virtual Value *emit(llvm::ArrayRef<llvm::Value *> Operands,
                      IntrinsicBuilder &Builder) const override;
  float getCost(TargetTransformInfo *TTI, LLVMContext &Ctx) const override;
};

// Aux class enumerating vector ir that we can emit
class IRInstTable {
  std::vector<BinaryIROperation> VectorizableOps;
  std::vector<IRVectorBinding> VectorInsts;
  std::vector<InstBinding *> Bindings;

public:
  IRInstTable();
  llvm::ArrayRef<InstBinding *> getBindings() const { return Bindings; }
};

#endif // end IR_VEC_H
