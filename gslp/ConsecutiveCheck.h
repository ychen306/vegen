#ifndef CONSECUTIVE_CHECK_H
#define CONSECUTIVE_CHECK_H

namespace llvm {
class Instruction;
class DataLayout;
class ScalarEvolution;
class LoopInfo;
} // namespace llvm

bool isConsecutive(llvm::Instruction *A, llvm::Instruction *B,
                   const llvm::DataLayout &DL, llvm::ScalarEvolution &SE,
                   llvm::LoopInfo &LI);

#endif
