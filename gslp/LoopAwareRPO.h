#ifndef LOOP_AWARE_RPO_H
#define LOOP_AWARE_RPO_H

#include "llvm/ADT/SmallVector.h"

namespace llvm {
class BasicBlock;
class Function;
class LoopInfo;
} // namespace llvm

void computeRPO(llvm::Function *, llvm::LoopInfo &,
                llvm::SmallVectorImpl<llvm::BasicBlock *> &);

#endif // LOOP_AWARE_RPO_H
