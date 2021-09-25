#ifndef REDUCTION_H
#define REDUCTION_H

#include "llvm/ADT/Optional.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/IVDescriptors.h"

namespace llvm {
class LoopInfo;
}

// Match for a loop reduction and return the non-phi values being reduced
llvm::Optional<llvm::RecurKind>
matchLoopReduction(llvm::PHINode *, llvm::LoopInfo &,
                   llvm::SmallVectorImpl<llvm::Value *> &Elts);

#endif // REDUCTION_H
