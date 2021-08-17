#include "CodeMotionUtil.h"
#include "ControlEquivalence.h"
#include "LoopFusion.h"
#include "llvm/ADT/EquivalenceClasses.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/Analysis/PostDominators.h"
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

// Find the innermost loop that contains both BB1 and BB2
static Loop *findCommonParentLoop(BasicBlock *BB1, BasicBlock *BB2,
                                  LoopInfo &LI) {
  for (Loop *L = LI.getLoopFor(BB1); L; L = L->getParentLoop())
    if (L->contains(BB2))
      return L;
  return nullptr;
}

static BasicBlock *getIDom(DominatorTree &DT, BasicBlock *BB) {
  auto *Node = DT.getNode(BB);
  if (Node == DT.getRootNode())
    return nullptr;
  return Node->getIDom()->getBlock();
}

// Find a dominator for BB that's also control-compatible for I
static BasicBlock *findCompatibleDominatorFor(Instruction *I, BasicBlock *BB,
                                              LoopInfo &LI, DominatorTree &DT,
                                              PostDominatorTree &PDT,
                                              ScalarEvolution &SE,
                                              DependenceInfo &DI) {
  for (; BB; BB = getIDom(DT, BB))
    if (isControlCompatible(I, BB, LI, DT, PDT, SE, DI))
      return BB;
  return nullptr;
}

namespace {
template <typename T>
SmallVector<T> getMembers(const EquivalenceClasses<T> &EC, T X) {
  auto It = EC.findLeader(X);
  if (It == EC.member_end())
    return {X};
  return SmallVector<T>(It, EC.member_end());
}
} // namespace

void hoistTo(Instruction *I, BasicBlock *BB, LoopInfo &LI, ScalarEvolution &SE,
             DominatorTree &DT, PostDominatorTree &PDT, DependenceInfo &DI,
             const EquivalenceClasses<Instruction *> &CoupledInsts) {
  // If I and BB are not in the same inner-loop, fuse the loops first
  Loop *LoopForI = LI.getLoopFor(I->getParent());
  Loop *LoopForBB = LI.getLoopFor(BB);
  assert(LoopForI == LoopForBB ||
         !isUnsafeToFuse(LoopForI, LoopForBB, LI, SE, DI, DT, PDT));
  if (LoopForI != LoopForBB)
    fuseLoops(LoopForI, LoopForBB, LI, DT, PDT, DI, SE);

  Loop *L = LI.getLoopFor(I->getParent());
  assert(L == LI.getLoopFor(BB) && "loop-fusion failed");
  assert(comesBefore(BB, I->getParent(), L));

  // TODO: order the dependences in topological order for efficiency
  SmallPtrSet<Instruction *, 16> Dependences;
  findDependencies(I, BB, L, DT, DI, Dependences);

  for (Instruction *Dep : Dependences) {
    if (Dep == I)
      continue;

    // Don't need to hoist the dependence if it already dominates `BB`
    if (DT.dominates(Dep, BB))
      continue;

    SmallVector<Instruction *> Coupled = getMembers(CoupledInsts, Dep);
    // Find a common dominator for the instructions (which we need to hoist as
    // well) coupled with `Dep`.
    BasicBlock *Dominator = BB;
    for (Instruction *I2 : Coupled) {
      Dominator =
          findCompatibleDominatorFor(I2, Dominator, LI, DT, PDT, SE, DI);
      assert(Dominator && "can't find a dominator to hoist dependence");
    }

    // Hoist `Dep` and its coupled instructions to the common dominator
    for (Instruction *I2 : Coupled)
      hoistTo(I2, Dominator, LI, SE, DT, PDT, DI, CoupledInsts);
  }
  I->moveBefore(BB->getTerminator());
}

bool isControlCompatible(Instruction *I, BasicBlock *BB, LoopInfo &LI,
                         DominatorTree &DT, PostDominatorTree &PDT,
                         ScalarEvolution &SE, DependenceInfo &DI) {
  if (!isControlEquivalent(*I->getParent(), *BB, DT, PDT))
    return false;

  Loop *LoopForI = LI.getLoopFor(I->getParent());
  Loop *LoopForBB = LI.getLoopFor(BB);
  if (LoopForI != LoopForBB &&
      isUnsafeToFuse(LoopForI, LoopForBB, LI, SE, DI, DT, PDT))
    return false;

  // Find dependences of `I` that comes after `BB`
  SmallPtrSet<Instruction *, 16> Dependences;
  findDependencies(I, BB, findCommonParentLoop(I->getParent(), BB, LI), DT, DI,
                   Dependences);

  for (Instruction *Dep : Dependences)
    if (Dep != I && !findCompatibleDominatorFor(Dep, BB, LI, DT, PDT, SE, DI))
      return false;

  return true;
}
