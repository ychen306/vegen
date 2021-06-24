#ifndef INTRINSIC_BUILDER_H
#define INTRINSIC_BUILDER_H

#include "llvm/IR/IRBuilder.h"

class IntrinsicBuilder : public llvm::IRBuilder<> {
  llvm::Module &InstWrappers;

public:
  llvm::LLVMContext &getContext() { return InstWrappers.getContext(); }
  using InsertPoint = llvm::IRBuilderBase::InsertPoint;
  IntrinsicBuilder(llvm::Module &InstWrappers)
      : llvm::IRBuilder<>(InstWrappers.getContext()),
        InstWrappers(InstWrappers) {}

  llvm::Value *Create(llvm::StringRef Name,
                      llvm::ArrayRef<llvm::Value *> Operands,
                      unsigned char Imm8 = 0);
};

#endif // end INTRINSIC_BUILDER_H
