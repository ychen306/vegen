#ifndef SCALARIZER_H
#define SCALARIZER_H
// Our patched version of llvm Scalarizer to avoid scalarizing invokes that returns scalar instructions
llvm::FunctionPass *createVeGenScalarizerPass();
#endif
