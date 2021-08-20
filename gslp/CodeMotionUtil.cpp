#include "CodeMotionUtil.h"
#include "ControlEquivalence.h"
#include "LoopFusion.h"
#include "llvm/ADT/BreadthFirstIterator.h"
#include "llvm/ADT/EquivalenceClasses.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Transforms/Utils/PromoteMemToReg.h"

using namespace llvm;

// FIXME: rewrite this to ignore *all* backedges
bool comesBefore(BasicBlock *BB1, BasicBlock *BB2, Loop *ParentLoop) {
  SmallPtrSet<BasicBlock *, 8> Visited;
  // mark the loop header as visited to avoid visiting the backedge
  if (ParentLoop)
    Visited.insert(ParentLoop->getHeader());

  SmallVector<BasicBlock *, 8> Worklist;
  Worklist.append(succ_begin(BB1), succ_end(BB1));

  while (!Worklist.empty()) {
    BasicBlock *BB = Worklist.pop_back_val();
    if (!Visited.insert(BB).second)
      continue;
    if (BB == BB2)
      return true;
    Worklist.append(succ_begin(BB), succ_end(BB));
  }
  return false;
}

static bool comesBefore(Instruction *I1, Instruction *I2, Loop *ParentLoop) {
  BasicBlock *BB1 = I1->getParent();
  BasicBlock *BB2 = I2->getParent();
  if (BB1 == BB2)
    return I1->comesBefore(I2);
  return comesBefore(BB1, BB2, ParentLoop);
}

static void getBlocksReachableFrom(
    BasicBlock *Earliest, SmallPtrSetImpl<BasicBlock *> &Reachable,
    const DenseSet<std::pair<BasicBlock *, BasicBlock *>> &BackEdges) {
  SmallVector<BasicBlock *> Worklist;
  SmallPtrSet<BasicBlock *, 16> Visited;
  auto ProcessSuccessors = [&](BasicBlock *BB) {
    for (auto *Succ : successors(BB))
      if (!BackEdges.count({BB, Succ}))
        Worklist.push_back(Succ);
  };
  ProcessSuccessors(Earliest);
  while (!Worklist.empty()) {
    BasicBlock *BB = Worklist.pop_back_val();
    if (Reachable.insert(BB).second)
      ProcessSuccessors(BB);
  }
}

static void getBlocksReaching(
    BasicBlock *Latest, SmallPtrSetImpl<BasicBlock *> &CanComeFrom,
    const DenseSet<std::pair<BasicBlock *, BasicBlock *>> &BackEdges) {
  SmallVector<BasicBlock *> Worklist;
  SmallPtrSet<BasicBlock *, 16> Visited;
  auto ProcessPreds = [&](BasicBlock *BB) {
    for (auto *Pred : predecessors(BB))
      if (!BackEdges.count({Pred, BB}))
        Worklist.push_back(Pred);
  };
  ProcessPreds(Latest);
  while (!Worklist.empty()) {
    BasicBlock *BB = Worklist.pop_back_val();
    if (CanComeFrom.insert(BB).second)
      ProcessPreds(BB);
  }
}

void getInBetweenInstructions(Instruction *I, BasicBlock *Earliest,
                              LoopInfo *LI,
                              SmallPtrSetImpl<Instruction *> &InBetweenInsts) {
  DenseSet<std::pair<BasicBlock *, BasicBlock *>> BackEdges;
  if (LI) {
    for (Loop *L = LI->getLoopFor(I->getParent()); L; L = L->getParentLoop()) {
      assert(L->getLoopLatch() && "loop doesn't have unique latch");
      BackEdges.insert({L->getLoopLatch(), L->getHeader()});
    }
  }

  SmallPtrSet<BasicBlock *, 16> ReachableFromEarliest, CanReachI;
  getBlocksReachableFrom(Earliest, ReachableFromEarliest, BackEdges);
  getBlocksReaching(I->getParent(), CanReachI, BackEdges);

  for (auto *BB : ReachableFromEarliest) {
    if (BB == Earliest || !CanReachI.count(BB))
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

    for (auto &I2 : *I->getParent()) {
      if (!I2.comesBefore(I))
        break;
      InBetweenInsts.insert(&I2);
    }
  }
}

// FIXME: treat reduction as special cases
// FIXME: ignore cycles backedge coming from phi nodes
// Find instructions from `Earliest until `I that `I depends on
// FIXME: rewrite this to ignore *all* backedges (i.e.
// FIXME: support Earliest being null
void findDependences(Instruction *I, BasicBlock *Earliest, LoopInfo &LI,
                     DominatorTree &DT, DependenceInfo &DI,
                     SmallPtrSetImpl<Instruction *> &Depended, bool Inclusive) {
  SmallPtrSet<Instruction *, 16> InBetweenInsts;
  getInBetweenInstructions(I, Earliest, &LI, InBetweenInsts);

  SmallVector<Instruction *> Worklist{I};
  while (!Worklist.empty()) {
    Instruction *I = Worklist.pop_back_val();

    if (!Inclusive && DT.dominates(I, Earliest->getTerminator()))
      continue;

    if (Inclusive && DT.properlyDominates(I->getParent(), Earliest))
      continue;

    if (!Depended.insert(I).second)
      continue;

    for (Value *V : I->operand_values()) {
      // Ignore loop carried dependences, which can only come from phi nodes
      auto *OpInst = dyn_cast<Instruction>(V);
      if (OpInst && DT.dominates(I, OpInst)) {
        assert(isa<PHINode>(I));
        continue;
      }

      if (OpInst)
        Worklist.push_back(OpInst);
    }

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

BasicBlock *findCompatiblePredecessorsFor(Instruction *I, BasicBlock *BB,
                                          LoopInfo &LI, DominatorTree &DT,
                                          PostDominatorTree &PDT,
                                          DependenceInfo &DI,
                                          ScalarEvolution *SE, bool Inclusive) {
  Loop *ParentLoop = findCommonParentLoop(I->getParent(), BB, LI);
  SkipBackEdge SBE(ParentLoop);
  for (BasicBlock *Pred : inverse_depth_first_ext(BB, SBE)) {
    if (!Inclusive && Pred == BB)
      continue;
    if (isControlCompatible(I, Pred, LI, DT, PDT, DI, SE))
      return Pred;
  }
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
  if (I->getParent() == BB)
    return;
  // If I and BB are not in the same inner-loop, fuse the loops first
  Loop *LoopForI = LI.getLoopFor(I->getParent());
  Loop *LoopForBB = LI.getLoopFor(BB);
  assert(LoopForI == LoopForBB ||
         !isUnsafeToFuse(LoopForI, LoopForBB, LI, SE, DI, DT, PDT));
  if (LoopForI != LoopForBB)
    fuseLoops(LoopForI, LoopForBB, LI, DT, PDT, SE, DI);

  Loop *L = LI.getLoopFor(I->getParent());
  assert(L == LI.getLoopFor(BB) && "loop-fusion failed");

  // TODO: order the dependences in topological order for efficiency
  SmallPtrSet<Instruction *, 16> Dependences;
  BasicBlock *Dominator = DT.findNearestCommonDominator(I->getParent(), BB);
  findDependences(
      I, Dominator, LI, DT, DI, Dependences,
      isa<PHINode>(I) /* include the dep found in BB if it's a phi node*/);

  for (Instruction *Dep : Dependences) {
    if (Dep == I)
      continue;

    // Don't need to hoist the dependence if it already comes before `BB`
    if (comesBefore(Dep, BB->getTerminator(), L) &&
        (!isa<PHINode>(I) || Dep->getParent() != BB))
      continue;

    SmallVector<Instruction *> Coupled = getMembers(CoupledInsts, Dep);
    // Find a common dominator for the instructions (which we need to hoist as
    // well) coupled with `Dep`.
    BasicBlock *Dominator = BB;
    for (Instruction *I2 : Coupled) {
      // We need to hoist the dependence of a phi node *before* the target block
      bool Inclusive = !isa<PHINode>(I);
      Dominator = findCompatiblePredecessorsFor(I2, Dominator, LI, DT, PDT, DI,
                                                &SE, Inclusive);
      assert(Dominator && "can't find a dominator to hoist dependence");
    }

    // Hoist `Dep` and its coupled instructions to the common dominator
    for (Instruction *I2 : Coupled)
      hoistTo(I2, Dominator, LI, SE, DT, PDT, DI, CoupledInsts);
  }

  auto *PN = dyn_cast<PHINode>(I);
  if (!PN) {
    I->moveBefore(BB->getTerminator());
    return;
  }

  PN->moveBefore(BB->getFirstNonPHI());
  // Replace the old incoming blocks with the control-equivalent preds of BB
  for (BasicBlock *Incoming : PN->blocks()) {
    auto PredIt = find_if(predecessors(BB), [&](BasicBlock *Pred) {
      return isControlEquivalent(*Incoming, *Pred, DT, PDT);
    });
    assert(PredIt != pred_end(BB) &&
           "can't find equivalent incoming for hoisted phi");
    PN->replaceIncomingBlockWith(Incoming, *PredIt);
  }
}

// FIXME: PHI-node should have a stricter compatibility criterion
bool isControlCompatible(Instruction *I, BasicBlock *BB, LoopInfo &LI,
                         DominatorTree &DT, PostDominatorTree &PDT,
                         DependenceInfo &DI, ScalarEvolution *SE) {
  if (!isControlEquivalent(*I->getParent(), *BB, DT, PDT))
    return false;

  // PHI nodes needs to have their incoming blocks equivalent to some
  // predecessor of BB
  if (auto *PN = dyn_cast<PHINode>(I)) {
    for (BasicBlock *Incoming : PN->blocks()) {
      auto PredIt = find_if(predecessors(BB), [&](BasicBlock *Pred) {
        return isControlEquivalent(*Incoming, *Pred, DT, PDT);
      });
      if (PredIt == pred_end(BB))
        return false;
    }
  }

  Loop *LoopForI = LI.getLoopFor(I->getParent());
  Loop *LoopForBB = LI.getLoopFor(BB);
  if ((bool)LoopForI ^ (bool)LoopForBB)
    return false;
  if (LoopForI != LoopForBB &&
      (!SE || isUnsafeToFuse(LoopForI, LoopForBB, LI, *SE, DI, DT, PDT)))
    return false;

  // Find dependences of `I` that could get violated by hoisting `I` to `BB`
  SmallPtrSet<Instruction *, 16> Dependences;
  BasicBlock *Dominator = DT.findNearestCommonDominator(I->getParent(), BB);
  findDependences(I, Dominator, LI, DT, DI, Dependences);

  // FIXME: check for unsafe to hoist things
  for (Instruction *Dep : Dependences) {
    // We need to hoist the dependences of a phi node into a proper predecessor
    bool Inclusive = !isa<PHINode>(I);
    if (Dep != I &&
        !findCompatiblePredecessorsFor(Dep, BB, LI, DT, PDT, DI, SE, Inclusive))
      return false;
  }

  return true;
}

bool isControlCompatible(Instruction *I1, Instruction *I2, LoopInfo &LI,
                         DominatorTree &DT, PostDominatorTree &PDT,
                         DependenceInfo &DI, ScalarEvolution *SE) {
  Loop *ParentLoop = findCommonParentLoop(I1->getParent(), I2->getParent(), LI);
  if (comesBefore(I1, I2, ParentLoop))
    std::swap(I1, I2);
  return isControlCompatible(I1, I2->getParent(), LI, DT, PDT, DI, SE);
}

void fixDefUseDominance(Function *F, DominatorTree &DT) {
  // Find instructions not dominating their uses.
  // This happens when we move things across branches.
  DenseMap<Instruction *, SmallVector<Instruction *, 4>> BrokenUseDefs;
  for (Instruction &I : instructions(F)) {
    for (User *U : I.users()) {
      // Special case when the user is a phi-node
      if (auto *PN = dyn_cast<PHINode>(U)) {
        BasicBlock *IncomingBlock;
        Value *IncomingValue;
        for (auto Incoming : zip(PN->blocks(), PN->incoming_values())) {
          std::tie(IncomingBlock, IncomingValue) = Incoming;
          if (IncomingValue == &I &&
              !DT.dominates(I.getParent(), IncomingBlock)) {
            BrokenUseDefs[&I].push_back(PN);
            break;
          }
        }
        continue;
      }

      auto *UserInst = dyn_cast<Instruction>(U);
      if (UserInst && !DT.dominates(&I, UserInst))
        BrokenUseDefs[&I].push_back(UserInst);
    }
  }

  SmallVector<AllocaInst *> Allocas;
  for (auto &KV : BrokenUseDefs) {
    Instruction *I = KV.first;
    ArrayRef<Instruction *> Users = KV.second;

    auto *Alloca = new AllocaInst(I->getType(), 0, I->getName() + ".mem",
                                  &*F->getEntryBlock().getFirstInsertionPt());
    new StoreInst(I, Alloca, I->getNextNode());
    Allocas.push_back(Alloca);
    for (Instruction *UserInst : Users) {
      if (auto *PN = dyn_cast<PHINode>(UserInst)) {
        // Need to do the reload in predecessor for the phinodes
        for (unsigned i = 0; i < PN->getNumIncomingValues(); i++) {
          Value *V = PN->getIncomingValue(i);
          if (V != I)
            continue;
          auto *Reload = new LoadInst(
              I->getType(), Alloca, I->getName() + ".reload",
              PN->getIncomingBlock(i)->getTerminator() /*insert before*/);
          PN->setIncomingValue(i, Reload);
        }
        continue;
      }
      auto *Reload =
          new LoadInst(I->getType(), Alloca, I->getName() + ".reload",
                       UserInst /*insert before*/);
      UserInst->replaceUsesOfWith(I, Reload);
    }
  }

  PromoteMemToReg(Allocas, DT);
  assert(!verifyFunction(*F, &errs()));
}

void gatherInstructions(Function *F,
                        const EquivalenceClasses<Instruction *> &EC,
                        LoopInfo &LI, DominatorTree &DT, PostDominatorTree &PDT,
                        ScalarEvolution &SE, DependenceInfo &DI) {
  // Do a top-sort of the equivalence classes of instructions
  DenseSet<Instruction *> Visited;
  SmallVector<EquivalenceClasses<Instruction *>::iterator> SortedClasses;
  std::function<void(Instruction *)> Visit = [&](Instruction *I) {
    if (!Visited.insert(I).second)
      return;

    // Find the dependences of all instructions belonging to the equivalence
    // class
    SmallPtrSet<Instruction *, 16> Dependences;
    for (Instruction *I2 : getMembers(EC, I))
      findDependences(I2, &F->getEntryBlock(), LI, DT, DI, Dependences,
                      true /*inclusive*/);

    for (Instruction *Dep : Dependences)
      Visit(Dep);

    auto It = EC.findValue(I);
    if (It != EC.end() && It->isLeader())
      SortedClasses.push_back(It);
  };

  for (auto &Member : EC)
    if (Member.isLeader())
      Visit(Member.getData());

  EquivalenceClasses<Instruction *> CoupledInsts;
  for (auto ClassIt : SortedClasses) {
    auto Members = make_range(EC.member_begin(ClassIt), EC.member_end());
    assert(ClassIt->isLeader());
    Instruction *Leader = ClassIt->getData();
    for (Instruction *I : drop_begin(Members)) {
      assert(isControlCompatible(I, Leader->getParent(), LI, DT, PDT, DI, &SE));
      hoistTo(I, Leader->getParent(), LI, SE, DT, PDT, DI, CoupledInsts);
    }
    for (Instruction *I : drop_begin(Members))
      CoupledInsts.unionSets(Leader, I);
  }
}
