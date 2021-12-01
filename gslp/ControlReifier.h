#ifndef CONTROL_REIFIER_H
#define CONTROL_REIFIER_H

#include "llvm/ADT/DenseMap.h"

namespace llvm {
class Instruction;
class LLVMContext;
} // namespace llvm

class VLoop;
class GlobalDependenceAnalysis;
class ControlCondition;

class ControlReifier {
  llvm::LLVMContext &Ctx;
  GlobalDependenceAnalysis &DA;
  llvm::DenseMap<std::pair<const ControlCondition *, VLoop *>, llvm::Value *>
      ReifiedValues;

  llvm::Value *reify(const ControlCondition *, VLoop *);

public:
  ControlReifier(llvm::LLVMContext &Ctx, GlobalDependenceAnalysis &DA)
      : Ctx(Ctx), DA(DA) {}
  void reifyConditionsInLoop(VLoop *);
  llvm::Value *getValue(const ControlCondition *, VLoop *);
};

#endif // CONTROL_REIFIER_H
