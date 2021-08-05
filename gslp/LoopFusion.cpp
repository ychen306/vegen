#include "LoopFusion.h"
#include "ControlEquivalence.h"
#include "UseDefIterator.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/Analysis/IVDescriptors.h" // RecurKind
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/PromoteMemToReg.h"

using namespace llvm;
using namespace llvm::PatternMatch;

namespace {
// Use this to do DFS without taking the backedge
struct SkipBackEdge : public df_iterator_default_set<BasicBlock *> {
  SkipBackEdge(Loop *L) {
    if (L) {
      assert(L->getLoopLatch());
      insert(L->getLoopLatch());
    }
  }
};

template <typename PatternTy, typename ValueTy> struct Capture_match {
  PatternTy P;
  ValueTy *&V;

  Capture_match(PatternTy P, ValueTy *&V) : P(P), V(V) {}

  template <typename OpTy> bool match(OpTy *Op) {
    if (P.match(Op)) {
      V = cast<ValueTy>(Op);
      return true;
    }
    return false;
  }
};

template <typename PatternTy, typename ValueTy>
Capture_match<PatternTy, ValueTy> m_Capture(PatternTy P, ValueTy *&V) {
  return Capture_match<PatternTy, ValueTy>(P, V);
}

template <typename LHSPattern, typename RHSPattern>
Optional<RecurKind> matchReduction(Value *V, LHSPattern LHS, RHSPattern RHS) {
  if (match(V, m_c_Add(LHS, RHS)))
    return RecurKind::Add;
  if (match(V, m_c_Mul(LHS, RHS)))
    return RecurKind::Mul;
  if (match(V, m_c_And(LHS, RHS)))
    return RecurKind::And;
  if (match(V, m_c_Or(LHS, RHS)))
    return RecurKind::Or;
  if (match(V, m_c_Xor(LHS, RHS)))
    return RecurKind::Xor;
  if (match(V, m_c_FAdd(LHS, RHS)))
    return RecurKind::FAdd;
  if (match(V, m_c_FMul(LHS, RHS)))
    return RecurKind::FMul;

  // there's no m_c_FMin/Max
  if (match(V, m_FMin(LHS, RHS)))
    return RecurKind::FMax;
  if (match(V, m_FMax(LHS, RHS)))
    return RecurKind::FMin;
  if (match(V, m_FMin(RHS, LHS)))
    return RecurKind::FMax;
  if (match(V, m_FMax(RHS, LHS)))
    return RecurKind::FMin;

  if (match(V, m_c_SMax(LHS, RHS)))
    return RecurKind::SMax;
  if (match(V, m_c_SMin(LHS, RHS)))
    return RecurKind::SMin;
  if (match(V, m_c_UMax(LHS, RHS)))
    return RecurKind::UMax;
  if (match(V, m_c_UMin(LHS, RHS)))
    return RecurKind::UMin;

  return None;
}

Value *stripTrivialPHI(Value *V) {
  auto *PN = dyn_cast<PHINode>(V);
  if (!PN || PN->getNumIncomingValues() != 1)
    return V;
  return stripTrivialPHI(PN->getIncomingValue(0));
}

template <typename StartPattern>
Optional<RecurKind> matchReductionWithStartValue(Value *V, StartPattern Pat,
                                                 LoopInfo &LI) {
  V = stripTrivialPHI(V);

  if (auto Kind = matchReduction(V, Pat, m_Value()))
    return Kind;

  Value *V1, *V2;
  if (auto Kind = matchReduction(V, m_Value(V1), m_Value(V2))) {
    auto Kind1 = matchReductionWithStartValue(V1, Pat, LI);
    if (Kind1 && *Kind1 == *Kind)
      return Kind;
    auto Kind2 = matchReductionWithStartValue(V2, Pat, LI);
    if (Kind2 && *Kind2 == *Kind)
      return Kind;
  }

  Loop *L = nullptr;
  auto *PN = dyn_cast<PHINode>(V);
  if (PN)
    L = LI.getLoopFor(PN->getParent());
  if (!L) {
    return None;
  }
  RecurrenceDescriptor RD;
  if (!RecurrenceDescriptor::isReductionPHI(PN, L, RD))
    return None;
  if (match(RD.getRecurrenceStartValue().getValPtr(), Pat))
    return RD.getRecurrenceKind();

  auto Kind =
      matchReductionWithStartValue(RD.getRecurrenceStartValue(), Pat, LI);
  if (!Kind || *Kind != RD.getRecurrenceKind()) {
    return None;
  }
  return Kind;
}

} // namespace

// FIXME: the load and store should be control flow eqeuivalent
// FIXME: there should be no other writes between the matched load and the
// original store
// FIXME: the value being stored should have no outside user
static Optional<RecurKind>
matchReductionForStore(StoreInst *SI, LoadInst *&Load, LoopInfo &LI) {
  Load = nullptr;
  auto TheLoad =
      m_Capture(m_OneUse(m_Load(m_Specific(SI->getPointerOperand()))), Load);
  Optional<RecurKind> Kind =
      matchReductionWithStartValue(SI->getValueOperand(), TheLoad, LI);
  assert(!Kind || Load);
  return Kind;
}

// Find a store that transitively uses LI and is control-flow equivalent
static StoreInst *findSink(LoadInst *LI, DominatorTree &DT,
                           PostDominatorTree &PDT) {
  auto *BB = LI->getParent();
  for (Value *V : depth_first(DefToUse(LI))) {
    auto *SI = dyn_cast<StoreInst>(V);
    if (SI && isControlEquivalent(*BB, *SI->getParent(), DT, PDT))
      return SI;
  }
  return nullptr;
}

static Optional<RecurKind> matchReductionForLoad(LoadInst *Load, StoreInst *&SI,
                                                 DominatorTree &DT,
                                                 PostDominatorTree &PDT,
                                                 LoopInfo &LI) {
  SI = findSink(Load, DT, PDT);
  if (!SI)
    return None;
  LoadInst *TheLoad;
  Optional<RecurKind> Kind = matchReductionForStore(SI, TheLoad, LI);
  if (!Kind || TheLoad != Load)
    return None;
  return Kind;
}

static void collectMemoryAccesses(
    BasicBlock *BB, LoopInfo &LI, SmallVectorImpl<Instruction *> &Accesses,
    DenseMap<Instruction *, RecurKind> &ReductionKinds, bool &UnsafeToFuse) {
  if (BB->hasAddressTaken()) {
    UnsafeToFuse = true;
    return;
  }

  for (auto &I : *BB) {
    if (I.mayThrow()) {
      UnsafeToFuse = true;
      return;
    }

    if (isa<CallBase>(&I) && I.mayHaveSideEffects()) {
      UnsafeToFuse = true;
      return;
    }

    auto *Load = dyn_cast<LoadInst>(&I);
    auto *SI = dyn_cast<StoreInst>(&I);
    if ((Load && Load->isVolatile()) || (SI && SI->isVolatile())) {
      UnsafeToFuse = true;
      return;
    }

    if (SI) {
      LoadInst *Load;
      if (Optional<RecurKind> Kind = matchReductionForStore(SI, Load, LI)) {
        ReductionKinds[SI] = *Kind;
        ReductionKinds[Load] = *Kind;
      }
    }

    if (I.mayReadOrWriteMemory())
      Accesses.push_back(&I);
  }
}

Value *emitReduction(RecurKind Kind, Value *A, Value *B,
                     Instruction *InsertBefore) {
  IRBuilder<> IRB(InsertBefore);
  switch (Kind) {
  case RecurKind::Add:
    return IRB.CreateAdd(A, B);
  case RecurKind::Mul:
    return IRB.CreateMul(A, B);
  case RecurKind::And:
    return IRB.CreateAnd(A, B);
  case RecurKind::Or:
    return IRB.CreateOr(A, B);
  case RecurKind::Xor:
    return IRB.CreateXor(A, B);
  case RecurKind::FAdd:
    return IRB.CreateFAdd(A, B);
  case RecurKind::FMul:
    return IRB.CreateFMul(A, B);
  default:
    llvm_unreachable("unsupport reduction kind");
  }
  return nullptr;
}

static bool checkLoop(Loop *L) {
  return L->getLoopPreheader() && L->getHeader() && L->getExitingBlock() &&
         L->getExitBlock() && L->getLoopLatch() && L->isRotatedForm() &&
         !L->isInvalid();
}

static BasicBlock *getLoopEntry(Loop *L) {
  return L->isGuarded() ? L->getLoopGuardBranch()->getParent()
                        : L->getLoopPreheader();
}

// FIXME: detect case where `I` is used by a conditional that's later joined by
// a PHINode later used by L
static bool isUsedByLoop(Instruction *I, Loop *L) {
  for (Value *V : depth_first(DefToUse(I))) {
    auto *I = dyn_cast<Instruction>(V);
    if (I && L->contains(I->getParent()))
      return true;
  }
  return false;
}

static void
getInBetweenInstructions(Instruction *I, BasicBlock *Earliest, Loop *ParentLoop,
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
static void findDependencies(Instruction *I, BasicBlock *Earliest,
                             Loop *ParentLoop, DominatorTree &DT,
                             DependenceInfo &DI,
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

// Check if we can hoist `I` before `L`.
// FIXME: this is broken in cases where with conditional load, which we cannot
// hoist
static bool isSafeToHoistBefore(Instruction *I, Loop *L, DominatorTree &DT,
                                PostDominatorTree &PDT, DependenceInfo &DI) {
  BasicBlock *Header = L->getHeader();
  SmallVector<Instruction *> Worklist{I};
  SmallPtrSet<Instruction *, 16> Visited;
  while (!Worklist.empty()) {
    Instruction *I = Worklist.pop_back_val();
    if (!Visited.insert(I).second)
      continue;

    // Don't need to hoist I if already before the loop
    if (DT.dominates(I, Header->getTerminator()))
      continue;

    // Can't hoist stuff in the loop itself
    if (L->contains(I->getParent()))
      return false;

    // Assume we can't hoist branches
    if (isa<PHINode>(I))
      return false;

    for (Value *V : I->operand_values())
      if (auto *OpInst = dyn_cast<Instruction>(V))
        Worklist.push_back(OpInst);

    // If `I` reads or writes memory, we also need to check its memory
    // dependencies Do this by collecting all intermediate instructions between
    // BB and I
    SmallPtrSet<Instruction *, 16> InBetweenInsts;
    // FIXME: this is broken because it considers spurious paths that are
    // infeasible.
    getInBetweenInstructions(I, Header, L->getParentLoop(), InBetweenInsts);

    bool SafeToSpeculate = isSafeToSpeculativelyExecute(I);
    for (auto *I2 : InBetweenInsts) {
      if (!SafeToSpeculate && I2->mayThrow())
        return false;

      auto Dep = DI.depends(I2, I, true);
      if (Dep && !Dep->isInput())
        Worklist.push_back(I2);
    }
  }
  return true;
}

static void
getIntermediateBlocks(Loop *L1, Loop *L2,
                      SmallVectorImpl<BasicBlock *> &IntermediateBlocks) {
  auto *ParentLoop = L1->getParentLoop();
  DenseSet<BasicBlock *> ReachesL2;
  SkipBackEdge SBE(ParentLoop);
  for (auto *BB : inverse_depth_first_ext(L2->getLoopPreheader(), SBE))
    ReachesL2.insert(BB);

  for (auto *BB : ReversePostOrderTraversal<BasicBlock *>(L1->getExitBlock()))
    if (ReachesL2.count(BB))
      IntermediateBlocks.push_back(BB);
}

// Return true is *independent*
// For the sake of checking there are unsafe memory accesses before L1 and L2,
// we also assume L1 comes before L2.
static bool checkDependencies(Loop *L1, Loop *L2, LoopInfo &LI,
                              DependenceInfo &DI, DominatorTree &DT,
                              PostDominatorTree &PDT) {
  // Collect the memory accesses
  SmallVector<Instruction *> Accesses1, Accesses2;
  DenseMap<Instruction *, RecurKind> ReductionKinds;
  bool UnsafeToFuse = false;
  for (auto *BB : L1->blocks()) {
    collectMemoryAccesses(BB, LI, Accesses1, ReductionKinds, UnsafeToFuse);
    if (UnsafeToFuse)
      return false;
  }
  for (auto *BB : L2->blocks()) {
    collectMemoryAccesses(BB, LI, Accesses2, ReductionKinds, UnsafeToFuse);
    if (UnsafeToFuse)
      return false;
  }

  // Blocks after L1 and before L2
  SmallVector<BasicBlock *, 8> IntermediateBlocks;
  getIntermediateBlocks(L1, L2, IntermediateBlocks);

  auto IsInL1 = [&](Instruction *I) { return L1->contains(I->getParent()); };
  BasicBlock *L1Entry = getLoopEntry(L1);

  for (BasicBlock *BB : IntermediateBlocks) {
    collectMemoryAccesses(BB, LI, Accesses1, ReductionKinds, UnsafeToFuse);
    if (UnsafeToFuse)
      return false;
    for (auto &I : *BB)
      if (isUsedByLoop(&I, L2) && !isSafeToHoistBefore(&I, L1, DT, PDT, DI))
        return false;
  }

  // Check the dependence
  for (auto *I1 : Accesses1)
    for (auto *I2 : Accesses2) {
      // We don't care about the dependence between a pair of reductions
      if (ReductionKinds.count(I1) && ReductionKinds.count(I2) &&
          ReductionKinds.lookup(I1) == ReductionKinds.lookup(I2))
        continue;
      auto Dep = DI.depends(I1, I2, true);
      if (Dep && !Dep->isInput()) {
        errs() << "Detected dependence from " << *I1 << " to " << *I2 << '\n';
        return false;
      }
    }
  return true;
}

bool isUnsafeToFuse(Loop *L1, Loop *L2, LoopInfo &LI, ScalarEvolution &SE,
                    DependenceInfo &DI, DominatorTree &DT,
                    PostDominatorTree &PDT) {
  if (!checkLoop(L1) || !checkLoop(L2)) {
    errs() << "Loops don't have the right shape\n";
    return true;
  }

  if (L1->getLoopDepth() != L2->getLoopDepth()) {
    errs() << "Loops have different nesting level\n";
    return true;
  }

  // Make sure the two loops have constant trip counts
  const SCEV *TripCount1 = SE.getBackedgeTakenCount(L1);
  const SCEV *TripCount2 = SE.getBackedgeTakenCount(L2);
  if (isa<SCEVCouldNotCompute>(TripCount1) ||
      isa<SCEVCouldNotCompute>(TripCount2) || TripCount1 != TripCount2) {
    errs() << "Loops may have divergent trip count\n";
    return true;
  }

  Loop *L1Parent = L1->getParentLoop();
  Loop *L2Parent = L2->getParentLoop();
  // If L1 and L2 are nested inside other loops, those loops also need to be
  // fused
  if (L1Parent != L2Parent) {
    if (isUnsafeToFuse(L1->getParentLoop(), L2->getParentLoop(), LI, SE, DI, DT,
                       PDT)) {
      errs() << "Parent loops can't be fused\n";
      return true;
    }
    // TODO: maybe support convergent control flow?
    // For now, don't fuse nested loops that are conditionally executed
    // (since it's harder to prove they are executed together)
    if (!isControlEquivalent(*L1->getParentLoop()->getHeader(),
                             *getLoopEntry(L1), DT, PDT) ||
        !isControlEquivalent(*L2->getParentLoop()->getHeader(),
                             *getLoopEntry(L2), DT, PDT)) {
      errs() << "Can't fuse conditional nested loop\n";
      return true;
    }
  } else {
    if (!isControlEquivalent(*L1->getLoopPreheader(), *L2->getLoopPreheader(),
                             DT, PDT)) {
      errs() << "Loops are not control flow equivalent\n";
      return true;
    }

    bool OneBeforeTwo = DT.dominates(getLoopEntry(L1), getLoopEntry(L2));
    if ((OneBeforeTwo && !checkDependencies(L1, L2, LI, DI, DT, PDT)) ||
        (!OneBeforeTwo && !checkDependencies(L2, L1, LI, DI, DT, PDT))) {
      errs() << "Loops are dependent (memory)\n";
      return true;
    }
  }

  if (!L1->isLCSSAForm(DT) || !L2->isLCSSAForm(DT)) {
    errs() << "Loops are not in LCSSA\n";
    return true;
  }

  // Check if one loop computes any SSA values that are used by another loop
  for (PHINode &PN : L1->getExitBlock()->phis())
    if (isUsedByLoop(&PN, L2)) {
      errs() << "Loops are dependent (ssa)\n";
      return true;
    }
  for (PHINode &PN : L2->getExitBlock()->phis())
    if (isUsedByLoop(&PN, L1)) {
      errs() << "Loops are dependent (ssa)\n";
      return true;
    }

  return false; // *probably* safe
}

static bool getNumPHIs(BasicBlock *BB) {
  return std::distance(BB->phis().begin(), BB->phis().end());
}

Loop *fuseLoops(Loop *L1, Loop *L2, LoopInfo &LI, DominatorTree &DT,
                PostDominatorTree &PDT, DependenceInfo &DI) {
  if (!checkLoop(L1) || !checkLoop(L2))
    return nullptr;

  // If L1 and L2 do not have a direct common parent, fuse their parents first.
  auto *L1Parent = L1->getParentLoop();
  auto *L2Parent = L2->getParentLoop();
  if (L1Parent != L2Parent) {
    assert(L1Parent && L2Parent && "L1 and L2 not nested evenly");
    fuseLoops(L1Parent, L2Parent, LI, DT, PDT, DI);
    L1->verifyLoop();
    L2->verifyLoop();
  }

  // If L1 doesn't come before L2, swap them.
  SkipBackEdge SBE(L1->getParentLoop());
  bool L1BeforeL2 =
      any_of(depth_first_ext(L1->getExitBlock(), SBE),
             [L2](BasicBlock *BB) { return BB == L2->getHeader(); });
  if (!L1BeforeL2) {
    std::swap(L1, L2);
    L1Parent = L1->getParentLoop();
    L2Parent = L2->getParentLoop();
  }

  BasicBlock *L1Preheader = L1->getLoopPreheader();
  BasicBlock *L2Preheader = L2->getLoopPreheader();
  BasicBlock *L1Header = L1->getHeader();
  BasicBlock *L2Header = L2->getHeader();
  BasicBlock *L1Latch = L1->getLoopLatch();
  BasicBlock *L2Latch = L2->getLoopLatch();
  BasicBlock *L1Exit = L1->getExitBlock();
  BasicBlock *L2Exit = L2->getExitBlock();

  // Find the set of instructions that L2 depends on and run after L1.
  // We need to hoist them before L1 and L2.
  SmallPtrSet<Instruction *, 16> L2Dependencies;
  DenseMap<Instruction *, SmallPtrSet<Instruction *, 8>> Users;
  // Keep track of code snippet that do something like `*x = *x + ...
  struct ReductionInfo {
    LoadInst *Load;
    StoreInst *Store;
    RecurKind Kind;
  };
  SmallVector<ReductionInfo> ReductionsToPatch;
  // Find the blocks that run after L1 and before L2
  SmallVector<BasicBlock *, 8> IntermediateBlocks;
  getIntermediateBlocks(L1, L2, IntermediateBlocks);
  for (auto *BB : IntermediateBlocks) {
    for (auto &I : *BB) {
      if (isUsedByLoop(&I, L2)) {
        // Detect reduction, in which case we don't need to the hosit
        // dependencies.
        auto *Load = dyn_cast<LoadInst>(&I);
        Optional<RecurKind> Kind = None;
        StoreInst *Store = nullptr;
        if (Load)
          Kind = matchReductionForLoad(Load, Store, DT, PDT, LI);
        if (Kind) {
          assert(Store);
          // Remember this reduction, and sink the load instead.
          // E.g., for something like:
          // ```
          //   writes
          //   x = load a
          //   v = x + something()
          //   store v
          // ```
          // We rewrite it into
          // ```
          //   v = 0 + something()
          //   writes
          //   x = load a
          //   v' = x + v
          //   store v'
          // ```
          ReductionsToPatch.push_back({Load, Store, *Kind});
          continue;
        }

        findDependencies(&I, L1Preheader /*Earliest possible dep*/, L1Parent,
                         DT, DI, L2Dependencies);
      }
    }
  }

  for (const ReductionInfo &RI : ReductionsToPatch) {
    Constant *Identity = RecurrenceDescriptor::getRecurrenceIdentity(
        RI.Kind, RI.Load->getType());
    RI.Load->replaceAllUsesWith(Identity);
    RI.Load->moveBefore(RI.Store);
    Value *V = RI.Store->getValueOperand();
    Value *Rdx = emitReduction(RI.Kind, V, RI.Load, RI.Store /*insert before*/);
    RI.Store->replaceUsesOfWith(V, Rdx);
  }

  // Compute a topological order for the dependencies we need to hoist.
  SmallVector<Instruction *> OrderedL2Dependencies;
  for (auto *BB : IntermediateBlocks)
    for (auto &I : *BB)
      if (L2Dependencies.count(&I)) {
        assert(!isa<PHINode>(&I) &&
               "can't fuse loops with intermediate phi deps");
        OrderedL2Dependencies.push_back(&I);
      }

  SmallVector<DominatorTree::UpdateType> CFGUpdates;
  auto RewriteBranch = [&](BasicBlock *Src, BasicBlock *OldDst,
                           BasicBlock *NewDst) {
    Src->getTerminator()->replaceUsesOfWith(OldDst, NewDst);
    CFGUpdates.push_back({DominatorTree::Insert, Src, NewDst});
    CFGUpdates.push_back({DominatorTree::Delete, Src, OldDst});
  };

  LLVMContext &Ctx = L1Preheader->getContext();
  Function *F = L1Preheader->getParent();
  // Create a placeholder block that will replace the loop header of L2
  BasicBlock *L2Placeholder =
      BasicBlock::Create(Ctx, L2Preheader->getName() + ".placeholder", F);
  BranchInst::Create(L2Exit /*to*/, L2Placeholder /*from*/);
  CFGUpdates.push_back({DominatorTree::Insert, L2Exit, L2Placeholder});

  assert(getNumPHIs(L1Preheader) == 0 && getNumPHIs(L2Preheader) == 0);

  // Rewrire all edges going into L2's preheader to, instead, go to
  // a dedicated placeholder for L2 that directly jumps to the L2's exit
  std::vector<BasicBlock *> Preds(pred_begin(L2Preheader),
                                  pred_end(L2Preheader));
  for (auto *BB : Preds)
    RewriteBranch(/*src=*/BB, /*old dst=*/L2Preheader,
                  /*new dst=*/L2Placeholder);

  // Run L2's preheader after L1's preheader
  RewriteBranch(/*src=*/L1Preheader, /*old dst=*/L1Header,
                /*new dst=*/L2Preheader);
  RewriteBranch(/*src=*/L2Preheader, /*old dst=*/L2Header,
                /*new dst=*/L1Header);

  // Run one iteration L2 after we are done with one iteration of L1
  assert(cast<BranchInst>(L1Latch->getTerminator())->isConditional());
  ReplaceInstWithInst(L1Latch->getTerminator(), BranchInst::Create(L2Header));
  CFGUpdates.push_back({DominatorTree::Delete, L1Latch, L1Header});
  CFGUpdates.push_back({DominatorTree::Delete, L1Latch, L1Exit});
  CFGUpdates.push_back({DominatorTree::Insert, L1Latch, L2Header});

  // hoist the PHI nodes in L2Header to L1Header
  while (auto *L2PHI = dyn_cast<PHINode>(&L2Header->front()))
    L2PHI->moveBefore(&*L1Header->getFirstInsertionPt());

  L1Header->replacePhiUsesWith(L1Preheader, L2Preheader);
  L1Header->replacePhiUsesWith(L1Latch, L2Latch);

  RewriteBranch(/*src=*/L2Latch, /*old dst=*/L2Header, /*new dst=*/L1Header);
  RewriteBranch(/*src=*/L2Latch, /*old dst=*/L2Exit, /*new dst=*/L1Exit);

  // Fix the PHIs contorlling the exit values
  L1Exit->replacePhiUsesWith(L1Latch, L2Latch);
  for (PHINode &PN : L2Exit->phis())
    for (unsigned i = 0; i < PN.getNumIncomingValues(); i++)
      if (PN.getIncomingBlock(i) == L2Latch)
        PN.setIncomingBlock(i, L2Placeholder);

  // Fix the dominance info, which we need to determine how to hoist L2's
  // dependencies.
  DT.applyUpdates(CFGUpdates);
  PDT.applyUpdates(CFGUpdates);

  // Hoist L2's dependencies
  for (Instruction *I : OrderedL2Dependencies) {
    Instruction *InsertPt =
        DT.findNearestCommonDominator(I->getParent(), L2Preheader)
            ->getTerminator();
    if (!DT.dominates(I, InsertPt)) {
      assert(!I->isTerminator());
      I->moveBefore(InsertPt);
    }
  }

  // Merge L2 into L1
  SmallVector<BasicBlock *> L2Blocks(L2->blocks());
  for (auto *BB : L2Blocks) {
    L1->addBlockEntry(BB);
    L2->removeBlockFromLoop(BB);
    if (LI.getLoopFor(BB) == L2)
      LI.changeLoopFor(BB, L1);
  }
  while (!L2->isInnermost()) {
    auto ChildLoopIt = L2->begin();
    Loop *ChildLoop = *ChildLoopIt;
    L2->removeChildLoop(ChildLoopIt);
    L1->addChildLoop(ChildLoop);
  }
  LI.erase(L2);
  // Add the placeholder block to the parent loop
  if (L1Parent)
    L1Parent->addBasicBlockToLoop(L2Placeholder, LI);

  // Go through the fused loop and find instructions not dominating their uses.
  // This happens when we move loops across branches (most notably their
  // original loop guards).
  DenseMap<Instruction *, SmallVector<Instruction *, 4>> BrokenUseDefs;
  for (auto *BB : L1->blocks())
    for (auto &I : *BB) {
      for (User *U : I.users()) {
        auto *UserInst = dyn_cast<Instruction>(U);
        if (UserInst && !L1->contains(UserInst) &&
            !DT.dominates(&I, UserInst)) {
          BrokenUseDefs[&I].push_back(UserInst);
        }
      }
    }
  for (auto &I : *L2Preheader) {
    for (User *U : I.users()) {
      auto *UserInst = dyn_cast<Instruction>(U);
      if (UserInst && !DT.dominates(&I, UserInst)) {
        BrokenUseDefs[&I].push_back(UserInst);
      }
    }
  }

  // Don't bother fixing the SSA invariant (def dom use) directly.
  // Just circumvent SSA with allocas
  // and then turning the allocas into PHI nodes with PromoteMemToReg.
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

  assert(L1->getLoopPreheader() == L2Preheader);
  assert(L1->getHeader() == L1Header);
  assert(L1->getLoopLatch() == L2Latch);
  assert(L1->getExitBlock() == L1Exit);

  assert(DT.verify());
  assert(PDT.verify());
  LI.verify(DT);
  assert(!verifyFunction(*F, &errs()));

  return L1;
}
