#include "UnrollFactor.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Transforms/Utils/Cloning.h"

using namespace llvm;

static Function *clone(const Function *F, ValueToValueMapTy &VMap) {
  auto FCopy = Function::Create(F->getFunctionType(), F->getLinkage(),
                                F->getAddressSpace());

  for (auto Pair : zip(F->args(), FCopy->args()))
    VMap[&std::get<0>(Pair)] = &std::get<1>(Pair);

  SmallVector<ReturnInst *> Returns;
  CloneFunctionInto(FCopy, F, VMap, false /*module level change*/, Returns);
  return FCopy;
}

void computeUnrollFactor(const Function *F, const LoopInfo &LI,
                         DenseMap<const Loop *, unsigned> &UFs) {
  ValueToValueMapTy VMap;
  Function *FCopy = clone(F, VMap);
}
