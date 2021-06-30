#ifndef SHUFFLE_OPT_H
#define SHUFFLE_OPT_H

namespace llvm {
class ShuffleVectorInst;
}

// return true if success
bool mergeShuffleVectors(llvm::ShuffleVectorInst *, llvm::ShuffleVectorInst *);

#endif // SHUFFLE_OPT_H
