#ifndef REIFY_CONTROL_CONDITION_H
#define REIFY_CONTROL_CONDITION_H

#include "llvm/ADT/DenseMap.h"

namespace llvm {
class Instruction;
class LLVMContext;
} // namespace llvm

class VLoop;
class GlobalDependenceAnalysis;
class ControlCondition;

// For a given control condition,
// insert instruction into VL to actually compute
// a boolean value that's equivalent to the control condition.
llvm::Instruction *reifyControlCondition(
    llvm::LLVMContext &, const ControlCondition *, VLoop *,
    GlobalDependenceAnalysis &,
    const llvm::DenseMap<const ControlCondition *, llvm::Instruction *>
        &CondToInstMap);

#endif // REIFY_CONTROL_CONDITION_H
