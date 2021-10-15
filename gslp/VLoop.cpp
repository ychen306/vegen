#include "VLoop.h"
#include "DependenceAnalysis.h"
#include "VectorPackContext.h"
#include "llvm/Analysis/LoopInfo.h"

using namespace llvm;

VLoop::VLoop(LoopInfo &LI, Loop *L, VectorPackContext *VPCtx, GlobalDependenceAnalysis *DA) : Depended(VPCtx->getNumValues()) {
  assert(L->isRotatedForm());
  // Build the subloops first
  for (auto *SubL : *L) {
    auto *SubVL = new VLoop(LI, SubL, VPCtx, DA);
    LoopStorage.emplace_back(SubVL);
    SubLoops.push_back(SubVL);
    Depended |= SubVL->getDepended();
  }

  llvm::BitVector InstSet(VPCtx->getNumValues());
  for (auto *BB : L->blocks()) {
    if (LI.getLoopFor(BB) != L)
      continue;
    for (auto &I : *BB) {
      Depended |= DA->getDepended(&I);
      Insts.push_back(&I);
      InstSet.set(VPCtx->getScalarId(&I));
    }
  }

  // Remove dependences that are in this loop
  InstSet.flip();
  Depended &= InstSet;
}
