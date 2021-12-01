#include "DependenceAnalysis.h"
#include "VLoop.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/IR/Constants.h"

using namespace llvm;

Instruction *reifyControlCondition(LLVMContext &Ctx,
    const ControlCondition *C, VLoop *VL, GlobalDependenceAnalysis &DA,
    const DenseMap<const ControlCondition *, Instruction *> &CondToInstMap) {
  assert(C);
}
