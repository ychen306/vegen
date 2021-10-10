#ifndef BLOCK_BUILDER_H
#define BLOCK_BUILDER_H

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallVector.h"

namespace llvm {
class LLVMContext;
class BasicBlock;
}

class ControlCondition;
class BlockBuilder {
  llvm::LLVMContext &Ctx;

  // Conditions with blocks that we can still modify
  llvm::DenseMap<const ControlCondition *, llvm::BasicBlock *> ActiveConds;

  // Conditions without modifiable blocks, but are used by blocks or used by other semi-active conds
  using ConditionVector = llvm::SmallVector<const ControlCondition *, 2>;
  llvm::DenseMap<const ControlCondition *, ConditionVector> SemiActiveConds;

  unsigned DummyCounter;
  const ControlCondition *getDummyCondition();

public:
  BlockBuilder(llvm::BasicBlock *EntryBB);
  llvm::BasicBlock *getBlockFor(const ControlCondition *);
};

#endif
