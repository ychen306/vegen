#ifndef CONSECUTIVE_CHECK_H
#define CONSECUTIVE_CHECK_H

#include "llvm/ADT/ArrayRef.h"

namespace llvm {
class Instruction;
class Value;
class DataLayout;
class ScalarEvolution;
class LoopInfo;
class SCEV;
template<typename T> class EquivalenceClasses;
} // namespace llvm

std::vector<std::pair<llvm::Instruction *, llvm::Instruction *>>
findConsecutiveAccesses(llvm::ScalarEvolution &SE, const llvm::DataLayout &DL,
                        llvm::ArrayRef<llvm::Instruction *>);

bool isConsecutive(llvm::Instruction *A, llvm::Instruction *B,
                   const llvm::DataLayout &DL, llvm::ScalarEvolution &SE,
                   llvm::LoopInfo &LI);

// Check if two pointers are equivalent
bool isEquivalent(llvm::Value *PtrA, llvm::Value *PtrB, llvm::ScalarEvolution &,
                  llvm::LoopInfo &);

std::vector<std::pair<llvm::Instruction *, llvm::Instruction *>>
findConsecutiveAccesses(llvm::ScalarEvolution &SE, const llvm::DataLayout &DL,
                        llvm::LoopInfo &LI,
                        llvm::ArrayRef<llvm::Instruction *> Accesses,
                        llvm::EquivalenceClasses<llvm::Instruction *> &EquivalentAccsses,
                        unsigned NumFingerprints = 4);

#endif
