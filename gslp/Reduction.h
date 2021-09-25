#ifndef REDUCTION_H
#define REDUCTION_H

#include "llvm/ADT/Optional.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/IVDescriptors.h"

namespace llvm {
class LoopInfo;
}

struct ReductionInfo {
  llvm::RecurKind Kind;
  llvm::PHINode *Phi;
  llvm::Value *StartValue;
  llvm::SmallVector<llvm::Value *, 4> Elts;      // things being reduced
  llvm::SmallVector<llvm::Instruction *, 4> Ops; // ops used to reduce things
};

// Match for a loop reduction and return the non-phi values being reduced
llvm::Optional<ReductionInfo> matchLoopReduction(llvm::PHINode *,
                                                 llvm::LoopInfo &);

#endif // REDUCTION_H
