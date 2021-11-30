#include "DependenceAnalysis.h"
#include "VLoop.h"
#include "llvm/ADT/DenseMap.h"

using namespace llvm;

Instruction *reifyControlCondition(
    const ControlCondition *C, VLoop *VL, GlobalDependenceAnalysis &DA,
    const DenseMap<const ControlCondition *, Instruction *> &CondToInstMap) {
}
