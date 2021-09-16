#define DEBUG_TYPE "vegen-motion-util"

#include "CodeMotionUtil.h"
#include "ControlEquivalence.h"
#include "DependenceAnalysis.h"
#include "LoopFusion.h"
#include "VectorPackContext.h"
#include "llvm/ADT/BreadthFirstIterator.h"
#include "llvm/ADT/EquivalenceClasses.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Transforms/Utils/PromoteMemToReg.h"

using namespace llvm;

ALWAYS_ENABLED_STATISTIC(NumCompatChecks,
                         "Number of control compatibility checks");

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

void getBlocksReachableFrom(
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

void getBlocksReaching(
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
// Find instructions from `Earliest until `I that `I depends on
void findDependences(Instruction *I, BasicBlock *Earliest, LoopInfo &LI,
                     DominatorTree &DT, LazyDependenceAnalysis &LDA,
                     SmallPtrSetImpl<Instruction *> &Depended, bool Inclusive) {
  SmallPtrSet<Instruction *, 16> InBetweenInsts;
  getInBetweenInstructions(I, Earliest, &LI, InBetweenInsts);

  auto *TheInst = I;
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

    for (auto *I2 : InBetweenInsts)
      if (LDA.depends(I2, I))
        Worklist.push_back(I2);
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

ControlCompatibilityChecker::ControlCompatibilityChecker(
    LoopInfo &LI, DominatorTree &DT, PostDominatorTree &PDT,
    LazyDependenceAnalysis &LDA, ScalarEvolution *SE, VectorPackContext *VPCtx,
    GlobalDependenceAnalysis *DA, bool PrecomputeEquivalentBlocks)
    : LI(LI), DT(DT), PDT(PDT), LDA(LDA), SE(SE), VPCtx(VPCtx), DA(DA),
      CheckEquivalentBlocksLazily(!PrecomputeEquivalentBlocks) {
  if (!PrecomputeEquivalentBlocks) {
    return;
  }

  // Compute block order
  Function *F = DT.getRootNode()->getBlock()->getParent();
  ReversePostOrderTraversal<Function *> RPO(F);
  unsigned i = 0;
  for (auto *BB : RPO)
    BlockOrder.try_emplace(BB, i++);
}

bool ControlCompatibilityChecker::isEquivalent(BasicBlock *BB1,
                                               BasicBlock *BB2) const {
  if (CheckEquivalentBlocksLazily || true) {
    if (EquivalentBlocks.isEquivalent(BB1, BB2))
      return true;
    if (isControlEquivalent(*BB1, *BB2, DT, PDT)) {
      EquivalentBlocks.unionSets(BB1, BB2);
      return true;
    }
    return false;
  }
  return EquivalentBlocks.isEquivalent(BB1, BB2);
}

BasicBlock *ControlCompatibilityChecker::findCompatiblePredecessorsFor(
    Instruction *I, BasicBlock *BB, bool Inclusive) const {
  BasicBlock *EarliestCompat = EarliestCompatibleBlocks.lookup(I);
  if (!CheckEquivalentBlocksLazily && EarliestCompat) {
    if (Inclusive && BlockOrder.lookup(EarliestCompat) <= BlockOrder.lookup(BB))
      return EarliestCompat;
    if (!Inclusive && BlockOrder.lookup(EarliestCompat) < BlockOrder.lookup(BB))
      return EarliestCompat;
  }

  Loop *ParentLoop = findCommonParentLoop(I->getParent(), BB, LI);
  SkipBackEdge SBE(ParentLoop);
  for (BasicBlock *Pred : inverse_depth_first_ext(BB, SBE)) {
    if (!Inclusive && Pred == BB)
      continue;
    if (isControlCompatible(I, Pred))
      return Pred;
  }
  return nullptr;
}

BasicBlock *findCompatiblePredecessorsFor(Instruction *I, BasicBlock *BB,
                                          LoopInfo &LI, DominatorTree &DT,
                                          PostDominatorTree &PDT,
                                          LazyDependenceAnalysis &LDA,
                                          ScalarEvolution *SE, bool Inclusive) {
  ControlCompatibilityChecker Checker(LI, DT, PDT, LDA, SE);
  return Checker.findCompatiblePredecessorsFor(I, BB, Inclusive);
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
             DominatorTree &DT, PostDominatorTree &PDT,
             LazyDependenceAnalysis &LDA,
             const EquivalenceClasses<Instruction *> &CoupledInsts) {
  // If I and BB are not in the same inner-loop, fuse the loops first
  Loop *LoopForI = LI.getLoopFor(I->getParent());
  Loop *LoopForBB = LI.getLoopFor(BB);
  assert(LoopForI == LoopForBB ||
         !isUnsafeToFuse(LoopForI, LoopForBB, LI, SE, LDA, DT, PDT));
  if (LoopForI != LoopForBB)
    fuseLoops(LoopForI, LoopForBB, LI, DT, PDT, SE, LDA);

  // Sometimes the loop fuser does the job
  if (I->getParent() == BB)
    return;

  Loop *L = LI.getLoopFor(I->getParent());
  assert(L == LI.getLoopFor(BB) && "loop-fusion failed");

  // TODO: order the dependences in topological order for efficiency
  SmallPtrSet<Instruction *, 16> Dependences;
  BasicBlock *Dominator = DT.findNearestCommonDominator(I->getParent(), BB);
  findDependences(
      I, Dominator, LI, DT, LDA, Dependences,
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
      Dominator = findCompatiblePredecessorsFor(I2, Dominator, LI, DT, PDT, LDA,
                                                &SE, Inclusive);
      if (!Dominator)
        abort();
      assert(Dominator && "can't find a dominator to hoist dependence");
    }

    // Hoist `Dep` and its coupled instructions to the common dominator
    for (Instruction *I2 : Coupled)
      hoistTo(I2, Dominator, LI, SE, DT, PDT, LDA, CoupledInsts);
  }

  auto *PN = dyn_cast<PHINode>(I);
  if (!PN) {
    I->moveBefore(BB->getTerminator());
    return;
  }

  PN->moveBefore(BB->getFirstNonPHI());
  // Replace the old incoming blocks with the control-equivalent preds of BB
  for (BasicBlock *Incoming : PN->blocks()) {
    auto *IncomingInst =
        dyn_cast<Instruction>(PN->getIncomingValueForBlock(Incoming));
    auto PredIt = find_if(predecessors(BB), [&](BasicBlock *Pred) {
      return (!IncomingInst ||
              comesBefore(IncomingInst, Pred->getTerminator(), L)) &&
             isControlEquivalent(*Incoming, *Pred, DT, PDT);
    });
    assert(PredIt != pred_end(BB) &&
           "can't find equivalent incoming for hoisted phi");
    errs() << "Replacing " << Incoming->getName() << " with "
           << (*PredIt)->getName() << " for " << *PN << '\n';
    PN->replaceIncomingBlockWith(Incoming, *PredIt);
  }
}

bool ControlCompatibilityChecker::isUnsafeToFuse(Loop *L1, Loop *L2) const {
  if (L1 < L2)
    std::swap(L1, L2);

  auto It = FusionMemo.find({L1, L2});
  if (It != FusionMemo.end())
    return It->second;

  return FusionMemo[{L1, L2}] =
             ::isUnsafeToFuse(L1, L2, LI, *SE, LDA, DT, PDT, this);
}

bool ControlCompatibilityChecker::isControlCompatible(Instruction *I,
                                                      BasicBlock *BB) const {
  auto MemoKey = std::make_pair(I, BB);
  auto It = Memo.find(MemoKey);
  if (It != Memo.end())
    return It->second;

  if (!CheckEquivalentBlocksLazily)
    NumCompatChecks++;

  if (!isEquivalent(I->getParent(), BB))
    return Memo[MemoKey] = false;

  // PHI nodes needs to have their incoming blocks equivalent to some
  // predecessor of BB
  if (auto *PN = dyn_cast<PHINode>(I)) {
    if (PN->getNumIncomingValues() != pred_size(BB))
      return Memo[MemoKey] = false;

    for (BasicBlock *Incoming : PN->blocks()) {
      auto PredIt = find_if(predecessors(BB), [&](BasicBlock *Pred) {
        return isControlEquivalent(*Incoming, *Pred, DT, PDT);
      });
      if (PredIt == pred_end(BB))
        return Memo[MemoKey] = false;
    }
  }
  Loop *LoopForI = LI.getLoopFor(I->getParent());
  Loop *LoopForBB = LI.getLoopFor(BB);
  if ((bool)LoopForI ^ (bool)LoopForBB)
    return Memo[MemoKey] = false;
  if (LoopForI != LoopForBB && (!SE || isUnsafeToFuse(LoopForI, LoopForBB)))
    return Memo[MemoKey] = false;

  // Find dependences of `I` that could get violated by hoisting `I` to `BB`
  BasicBlock *Dominator = DT.findNearestCommonDominator(I->getParent(), BB);
  SmallPtrSet<Instruction *, 16> Dependences;
  if (DA && VPCtx) {
    bool Inclusive = isa<PHINode>(I);
    for (Value *V : VPCtx->iter_values(DA->getDepended(I))) {
      auto *Dep = cast<Instruction>(V);
      if (!Inclusive && DT.dominates(Dep, Dominator->getTerminator()))
        continue;
      if (Inclusive && DT.properlyDominates(Dep->getParent(), Dominator))
        continue;
      Dependences.insert(Dep);
    }
  } else {
    findDependences(I, Dominator, LI, DT, LDA, Dependences, isa<PHINode>(I));
  }

  // FIXME: check for unsafe to hoist things like volatile
  for (Instruction *Dep : Dependences) {
    if (LoopForI && !LoopForI->contains(Dep->getParent()))
      continue;
    // We need to hoist the dependences of a phi node into a proper predecessor
    bool Inclusive = !isa<PHINode>(I);
    if (Dep != I && !findCompatiblePredecessorsFor(Dep, BB, Inclusive)) {
      return Memo[MemoKey] = false;
    }
  }

  if (!CheckEquivalentBlocksLazily) {
    BasicBlock *EarliestCompat = EarliestCompatibleBlocks.lookup(I);
    if (EarliestCompat &&
        BlockOrder.lookup(BB) < BlockOrder.lookup(EarliestCompat))
      EarliestCompatibleBlocks[I] = BB;
    else if (!EarliestCompat)
      EarliestCompatibleBlocks[I] = BB;
  }

  return Memo[MemoKey] = true;
}

bool isControlCompatible(Instruction *I, BasicBlock *BB, LoopInfo &LI,
                         DominatorTree &DT, PostDominatorTree &PDT,
                         LazyDependenceAnalysis &LDA, ScalarEvolution *SE) {
  ControlCompatibilityChecker Checker(LI, DT, PDT, LDA, SE);
  return Checker.isControlCompatible(I, BB);
}

bool isControlCompatible(Instruction *I1, Instruction *I2, LoopInfo &LI,
                         DominatorTree &DT, PostDominatorTree &PDT,
                         LazyDependenceAnalysis &LDA, ScalarEvolution *SE) {
  Loop *ParentLoop = findCommonParentLoop(I1->getParent(), I2->getParent(), LI);
  if (comesBefore(I1, I2, ParentLoop))
    std::swap(I1, I2);
  return isControlCompatible(I1, I2->getParent(), LI, DT, PDT, LDA, SE);
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
                        ScalarEvolution &SE, LazyDependenceAnalysis &LDA,
                        GlobalDependenceAnalysis *DA,
                        const VectorPackContext *VPCtx) {
  // Do a top-sort of the equivalence classes of instructions
  DenseSet<Instruction *> Visited;
  SmallVector<EquivalenceClasses<Instruction *>::iterator> SortedClasses;
  std::function<void(Instruction *)> Visit = [&](Instruction *I) {
    if (!Visited.insert(I).second)
      return;

    // Find the dependences of all instructions in the same EC
    SmallPtrSet<Instruction *, 16> Dependences;

    if (!DA) {
      for (Instruction *I2 : getMembers(EC, I))
        findDependences(I2, &F->getEntryBlock(), LI, DT, LDA, Dependences,
                        true /*inclusive*/);

      for (Instruction *Dep : Dependences)
        Visit(Dep);
    } else {
      assert(VPCtx);
      for (Instruction *I2 : getMembers(EC, I))
        for (Value *Dep : VPCtx->iter_values(DA->getDepended(I2)))
          Visit(cast<Instruction>(Dep));
    }

    auto It = EC.findValue(I);
    if (It != EC.end() && It->isLeader())
      SortedClasses.push_back(It);
  };

  for (auto &Member : EC)
    if (Member.isLeader())
      Visit(Member.getData());

  auto ComesBefore = [&LI](Instruction *I1, Instruction *I2) {
    auto *L = findCommonParentLoop(I1->getParent(), I2->getParent(), LI);
    return comesBefore(I1, I2, L);
  };

  EquivalenceClasses<Instruction *> CoupledInsts;
  for (auto ClassIt : SortedClasses) {
    SmallVector<Instruction *, 8> Members(EC.member_begin(ClassIt),
                                          EC.member_end());
    stable_sort(Members, ComesBefore);
    Instruction *Leader = Members.front();
    for (Instruction *I : drop_begin(Members)) {
      if (I == Leader)
        continue;
      assert(
          isControlEquivalent(*I->getParent(), *Leader->getParent(), DT, PDT));
      assert(
          isControlCompatible(I, Leader->getParent(), LI, DT, PDT, LDA, &SE));
      hoistTo(I, Leader->getParent(), LI, SE, DT, PDT, LDA, CoupledInsts);
    }
    for (Instruction *I : Members)
      CoupledInsts.unionSets(Leader, I);
  }

  fixDefUseDominance(F, DT);
}

bool haveIdenticalTripCounts(const Loop *L1, const Loop *L2,
                             ScalarEvolution &SE) {
  if (L1 == L2)
    return true;

  auto *TripCount1 = SE.getBackedgeTakenCount(L1);
  auto *TripCount2 = SE.getBackedgeTakenCount(L2);
  if (!isa<SCEVCouldNotCompute>(TripCount1) &&
      !isa<SCEVCouldNotCompute>(TripCount2) && TripCount1 == TripCount2)
    return true;

  auto *BB1 = L1->getExitingBlock();
  if (!BB1)
    return false;

  auto *BB2 = L2->getExitingBlock();
  if (!BB2)
    return false;

  using namespace PatternMatch;

  Value *LHS1, *RHS1;
  ICmpInst::Predicate Pred1;
  if (!match(BB1->getTerminator(),
             m_Br(m_ICmp(Pred1, m_Value(LHS1), m_Value(RHS1)), m_BasicBlock(),
                  m_BasicBlock())))
    return false;

  Value *LHS2, *RHS2;
  ICmpInst::Predicate Pred2;
  if (!match(BB2->getTerminator(),
             m_Br(m_ICmp(Pred2, m_Value(LHS2), m_Value(RHS2)), m_BasicBlock(),
                  m_BasicBlock())))
    return false;

  if (Pred1 != Pred2)
    return false;

  if (RHS1 != RHS2)
    return false;

  auto *Expr1 = dyn_cast<SCEVAddRecExpr>(SE.getSCEV(LHS1));
  if (!Expr1 || !Expr1->isAffine() || Expr1->getLoop() != L1)
    return false;

  auto *Expr2 = dyn_cast<SCEVAddRecExpr>(SE.getSCEV(LHS2));
  if (!Expr2 || !Expr1->isAffine() || Expr2->getLoop() != L2)
    return false;

  return Expr1->getOperand(0) == Expr2->getOperand(0) &&
         Expr1->getOperand(1) == Expr2->getOperand(1);
}
