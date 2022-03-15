#ifndef VECTOR_COMBINER_H
#define VECTOR_COMBINER_H
#define VECTOR_COMBINER_H

namespace llvm {
class PassRegistry;
class Pass;
void initializeVectorCombinerPass(PassRegistry &);
} // namespace llvm

llvm::Pass *createVectorCombiner();

#endif // VECTOR_COMBINER_H
