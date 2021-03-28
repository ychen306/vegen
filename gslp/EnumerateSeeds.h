#ifndef ENUMERATE_SEEDS_H
#define ENUMERATE_SEEDS_H

#include "Canonicalizer.h"
#include "llvm/ADT/ArrayRef.h"

using AbstractSeedPack = std::vector<const Canonicalizer::Node *>;

namespace llvm {
class BasicBlock;
}

class InstBinding;
class Packer;
class Canonicalizer;

std::vector<AbstractSeedPack>
enumerateAbstractSeeds(Packer *, Canonicalizer *, llvm::BasicBlock *,
                       llvm::ArrayRef<Canonicalizer::Node *>);

#endif // end ENUMERATE_SEEDS_H
