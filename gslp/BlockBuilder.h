#ifndef BLOCK_BUILDER_H
#define BLOCK_BUILDER_H

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallVector.h"

namespace llvm {
class LLVMContext;
class Value;
class BasicBlock;
class Function;
} // namespace llvm

class ControlCondition;
class BlockBuilder {
  llvm::LLVMContext &Ctx;
  llvm::Function *F;
  std::function<llvm::Value *(llvm::Value *)> EmitCondition;

  // Conditions with blocks that we can still modify
  llvm::DenseMap<const ControlCondition *, llvm::BasicBlock *> ActiveConds;

  // Conditions without modifiable blocks, but are used by blocks or used by
  // other semi-active conds
  using ConditionVector = llvm::SmallVector<const ControlCondition *, 2>;
  llvm::DenseMap<const ControlCondition *, ConditionVector> SemiActiveConds;

  unsigned DummyCounter;
  const ControlCondition *getDummyCondition();

  llvm::BasicBlock *createBlock();

public:
  BlockBuilder(llvm::BasicBlock *EntryBB,
               std::function<llvm::Value *(llvm::Value *)> EmitCondition);
  llvm::BasicBlock *getBlockFor(const ControlCondition *);
  void setBlockForCondition(llvm::BasicBlock *, const ControlCondition *);
};

#endif
