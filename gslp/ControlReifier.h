#ifndef CONTROL_REIFIER_H
#define CONTROL_REIFIER_H

#include "llvm/ADT/DenseMap.h"

namespace llvm {
class Instruction;
class Value;
class LLVMContext;
} // namespace llvm

class VLoop;
class GlobalDependenceAnalysis;
class ControlCondition;

class ControlReifier {
  llvm::LLVMContext &Ctx;
  GlobalDependenceAnalysis &DA;
  llvm::SmallVector<llvm::Instruction *> InsertedInsts;
  llvm::DenseMap<std::pair<const ControlCondition *, VLoop *>, llvm::Value *>
      ReifiedValues;

public:
  ControlReifier(llvm::LLVMContext &Ctx, GlobalDependenceAnalysis &DA)
      : Ctx(Ctx), DA(DA) {}
  void reifyConditionsInLoop(VLoop *);
  llvm::Value *reify(const ControlCondition *, VLoop *);
  llvm::Value *getValue(const ControlCondition *, VLoop *);
  llvm::ArrayRef<llvm::Instruction *> getInsertedInsts() const { return InsertedInsts; }
};

#endif // CONTROL_REIFIER_H
