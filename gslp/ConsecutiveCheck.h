#ifndef CONSECUTIVE_CHECK_H
#define CONSECUTIVE_CHECK_H

namespace llvm {
class Instruction;
class Value;
class DataLayout;
class ScalarEvolution;
class LoopInfo;
} // namespace llvm

bool isConsecutive(llvm::Instruction *A, llvm::Instruction *B,
                   const llvm::DataLayout &DL, llvm::ScalarEvolution &SE,
                   llvm::LoopInfo &LI);

// Check if two pointers are equivalent
bool isEquivalent(llvm::Value *PtrA, llvm::Value *PtrB,
                  llvm::ScalarEvolution &, llvm::LoopInfo &);

#endif
