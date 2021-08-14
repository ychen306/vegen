#include "CodeMotionUtil.h"
#include "llvm/ADT/EquivalenceClasses.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/IR/Dominators.h"

using namespace llvm;

bool comesBefore(BasicBlock *BB1, BasicBlock *BB2, Loop *ParentLoop) {
  SkipBackEdge SBE(ParentLoop);
  for (auto *BB : depth_first_ext(BB1, SBE))
    if (BB == BB2)
      return true;
  return false;
}

void getInBetweenInstructions(Instruction *I, BasicBlock *Earliest,
                              Loop *ParentLoop,
                              SmallPtrSetImpl<Instruction *> &InBetweenInsts) {
  // Figure out the blocks reaching I without taking the backedge of the parent
  // loop
  SkipBackEdge BackwardSBE(ParentLoop);
  SmallPtrSet<BasicBlock *, 8> ReachesI;
  for (auto *BB : inverse_depth_first_ext(I->getParent(), BackwardSBE))
    ReachesI.insert(BB);

  SkipBackEdge SBE(ParentLoop);
  for (BasicBlock *BB : depth_first_ext(Earliest, SBE)) {
    if (BB == Earliest)
      continue;

    if (!ReachesI.count(BB))
      continue;

    if (BB == I->getParent()) {
      for (auto &I2 : *BB) {
        if (I->comesBefore(&I2))
          break;
        InBetweenInsts.insert(&I2);
      }
      continue;
    }

    for (auto &I2 : *BB)
      InBetweenInsts.insert(&I2);
  }
}

// FIXME: treat reduction as special cases
// Find instructions from `Earliest until `I that `I depends on
void findDependencies(Instruction *I, BasicBlock *Earliest, Loop *ParentLoop,
                      DominatorTree &DT, DependenceInfo &DI,
                      SmallPtrSetImpl<Instruction *> &Depended) {
  SmallPtrSet<Instruction *, 16> InBetweenInsts;
  getInBetweenInstructions(I, Earliest, ParentLoop, InBetweenInsts);

  SmallVector<Instruction *> Worklist{I};
  while (!Worklist.empty()) {
    Instruction *I = Worklist.pop_back_val();

    if (DT.dominates(I, Earliest->getTerminator()))
      continue;

    if (!Depended.insert(I).second)
      continue;

    for (Value *V : I->operand_values())
      if (auto *OpInst = dyn_cast<Instruction>(V))
        Worklist.push_back(OpInst);

    for (auto *I2 : InBetweenInsts) {
      auto Dep = DI.depends(I2, I, true);
      if (Dep && !Dep->isInput())
        Worklist.push_back(I2);
    }
  }
}

void hoistTo(Instruction *I, BasicBlock *BB, DominatorTree &DT,
             Loop *ParentLoop, DependenceInfo &DI,
             EquivalenceClasses<Instruction *> CoupledInsts) {
}
