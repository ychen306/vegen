#ifndef ENUMERATE_SEEDS_H
#define ENUMERATE_SEEDS_H

#include "Canonicalizer.h"
#include "llvm/ADT/ArrayRef.h"

namespace llvm {
class BasicBlock;
}

class InstBinding;
class Packer;
class Canonicalizer;

class OperandPack;

std::vector<OperandPack> enumerateSeeds(Packer *, Canonicalizer *,
                                        llvm::BasicBlock *,
                                        llvm::ArrayRef<Canonicalizer::Node *>);

#endif // end ENUMERATE_SEEDS_H
