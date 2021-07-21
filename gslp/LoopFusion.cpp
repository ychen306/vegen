#include "LoopFusion.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/PostDominators.h"

using namespace llvm;

bool isUnsafeToFuse(Loop &L1, Loop &L2, ScalarEvolution &SE, DependenceInfo &DI) {
  return true;
}
