#include "LoopFusion.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/Analysis/IVDescriptors.h" // RecurKind
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/CodeMoverUtils.h"

using namespace llvm;

namespace {

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

} // namespace

static Optional<RecurKind> matchReduction(StoreInst *SI, LoadInst *&LI) {
  Value *V = SI->getValueOperand();
  using namespace llvm::PatternMatch;

  LI = nullptr;
  auto TheLoad =
      m_Capture(m_OneUse(m_Load(m_Specific(SI->getPointerOperand()))), LI);

  RecurKind Kind;
  if (match(V, m_c_Add(TheLoad, m_Value())))
    Kind = RecurKind::Add;
  else if (match(V, m_c_Mul(TheLoad, m_Value())))
    Kind = RecurKind::Mul;
  else if (match(V, m_c_And(TheLoad, m_Value())))
    Kind = RecurKind::And;
  else if (match(V, m_c_Or(TheLoad, m_Value())))
    Kind = RecurKind::Or;
  else if (match(V, m_c_Xor(TheLoad, m_Value())))
    Kind = RecurKind::Xor;
  else if (match(V, m_c_FAdd(TheLoad, m_Value())))
    Kind = RecurKind::FAdd;
  else if (match(V, m_c_FMul(TheLoad, m_Value())))
    Kind = RecurKind::FMul;

  // there's no m_c_FMin/Max
  else if (match(V, m_FMin(TheLoad, m_Value())))
    Kind = RecurKind::FMax;
  else if (match(V, m_FMax(TheLoad, m_Value())))
    Kind = RecurKind::FMin;
  else if (match(V, m_FMin(m_Value(), TheLoad)))
    Kind = RecurKind::FMax;
  else if (match(V, m_FMax(m_Value(), TheLoad)))
    Kind = RecurKind::FMin;

  else if (match(V, m_c_SMax(TheLoad, m_Value())))
    Kind = RecurKind::SMax;
  else if (match(V, m_c_SMin(TheLoad, m_Value())))
    Kind = RecurKind::SMin;
  else if (match(V, m_c_UMax(TheLoad, m_Value())))
    Kind = RecurKind::UMax;
  else if (match(V, m_c_UMin(TheLoad, m_Value())))
    Kind = RecurKind::UMin;
  else
    return None;

  assert(LI);
  return Kind;
}

static void
collectMemoryAccesses(BasicBlock *BB, SmallVectorImpl<Instruction *> &Accesses,
                      DenseMap<Instruction *, RecurKind> &ReductionKinds,
                      bool &UnsafeToFuse) {
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

    auto *LI = dyn_cast<LoadInst>(&I);
    auto *SI = dyn_cast<StoreInst>(&I);
    if ((LI && LI->isVolatile()) || (SI && SI->isVolatile())) {
      UnsafeToFuse = true;
      return;
    }

    if (SI) {
      LoadInst *LI;
      if (Optional<RecurKind> Kind = matchReduction(SI, LI)) {
        ReductionKinds[SI] = *Kind;
        ReductionKinds[LI] = *Kind;
      }
    }

    if (I.mayReadOrWriteMemory())
      Accesses.push_back(&I);
  }
}

static bool checkLoop(Loop &L) {
  return L.getLoopPreheader() && L.getHeader() && L.getExitingBlock() &&
         L.getExitBlock() && L.getLoopLatch() && L.isRotatedForm() &&
         !L.isInvalid();
}

static BasicBlock *getLoopEntry(Loop &L) {
  return L.isGuarded() ? L.getLoopGuardBranch()->getParent()
                       : L.getLoopPreheader();
}

// FIXME: detect case where `I` is used by a conditional that's later joined by
// a PHINode later used by L
static bool isUsedByLoop(Instruction *I, Loop &L) {
  DenseSet<Instruction *> Visited; // Deal with cycles resulted from PHIs
  std::function<bool(Instruction *)> IsUsed = [&](Instruction *I) -> bool {
    if (!Visited.insert(I).second)
      return false; // ignore backedge

    if (L.contains(I->getParent()))
      return true;

    for (User *U : I->users()) {
      auto *UI = dyn_cast<Instruction>(U);
      if (UI && IsUsed(UI))
        return true;
    }

    return false;
  };

  return IsUsed(I);
}

static void getInBetweenInstructions(Instruction *Begin, Instruction *End,
                                     SmallPtrSetImpl<Instruction *> &Insts) {
  SmallPtrSet<Instruction *, 16> Worklist;
  Worklist.insert(Begin);

  while (!Worklist.empty()) {
    auto *I = *Worklist.begin();
    Worklist.erase(I);

    if (I == End)
      continue;

    if (!Insts.insert(I).second)
      continue;

    if (auto *Next = I->getNextNode())
      Worklist.insert(Next);
    else {
      for (BasicBlock *BB : successors(I))
        Worklist.insert(&BB->front());
    }
  }
}

// Precondition: I and BB are control-flow equivalent
static bool isSafeToHoistBefore(Instruction *I, BasicBlock *BB,
                                std::function<bool(Instruction *)> CannotHoist,
                                DominatorTree &DT, PostDominatorTree &PDT,
                                DependenceInfo &DI) {
  DenseMap<Instruction *, bool> Memo;
  std::function<bool(Instruction *)> IsSafeToHoist = [&](Instruction *I) {
    auto It = Memo.find(I);
    if (It != Memo.end())
      return It->second;

    // Assume we can't hoist branches
    if (isa<PHINode>(I))
      return Memo[I] = false;

    if (CannotHoist(I))
      return Memo[I] = false;

    // Don't need to hoist I if already before BB
    if (DT.dominates(I, BB->getTerminator())) {
      return Memo[I] = true;
    }

    for (Value *V : I->operand_values()) {
      auto *OpInst = dyn_cast<Instruction>(V);
      if (OpInst && !IsSafeToHoist(OpInst))
        return Memo[I] = false;
    }

    // If `I` reads or writes memory, we also need to check its memory
    // dependencies Do this by collecting all intermediate instructions between
    // BB and I
    SmallPtrSet<Instruction *, 16> InBetweenInsts;
    getInBetweenInstructions(BB->getTerminator(), I, InBetweenInsts);

    bool SafeToSpeculate = isSafeToSpeculativelyExecute(I);
    for (auto *I2 : InBetweenInsts) {
      if (!SafeToSpeculate && I2->mayThrow())
        return Memo[I] = false;
      auto Dep = DI.depends(I2, I, true);
      if (Dep && !Dep->isInput() && !IsSafeToHoist(I2)) {
        return Memo[I] = false;
      }
    }

    return Memo[I] = true;
  };

  return IsSafeToHoist(I);
}

// Return true is *independent*
// For the sake of checking there are unsafe memory accesses before L1 and L2,
// we also assume L1 comes before L2.
static bool checkDependencies(Loop &L1, Loop &L2, DependenceInfo &DI,
                              DominatorTree &DT, PostDominatorTree &PDT) {
  // Collect the memory accesses
  SmallVector<Instruction *> Accesses1, Accesses2;
  DenseMap<Instruction *, RecurKind> ReductionKinds;
  bool UnsafeToFuse = false;
  for (auto *BB : L1.blocks()) {
    collectMemoryAccesses(BB, Accesses1, ReductionKinds, UnsafeToFuse);
    if (UnsafeToFuse)
      return false;
  }
  for (auto *BB : L2.blocks()) {
    collectMemoryAccesses(BB, Accesses2, ReductionKinds, UnsafeToFuse);
    if (UnsafeToFuse)
      return false;
  }

  BasicBlock *L1Exit = L1.getExitBlock();
  BasicBlock *L1Entry = getLoopEntry(L1);
  BasicBlock *L2Entry = getLoopEntry(L2);

  // Blocks after L1 and before L2
  DenseSet<BasicBlock *> IntermediateBlocks;
  for (BasicBlock *BB : depth_first(L1Exit)) {
    // We know L2 post dominates L1.
    // Therefore if L2 doesn't dominate BB, then BB must happen after L2.
    if (PDT.dominates(L2Entry, BB))
      IntermediateBlocks.insert(BB);
  }
  IntermediateBlocks.insert(L2.getLoopPreheader());

  auto IsInL1 = [&](Instruction *I) { return L1.contains(I->getParent()); };

  for (BasicBlock *BB : IntermediateBlocks) {
    collectMemoryAccesses(BB, Accesses1, ReductionKinds, UnsafeToFuse);
    if (UnsafeToFuse)
      return false;
    for (auto &I : *BB)
      if (isUsedByLoop(&I, L2) &&
          !isSafeToHoistBefore(&I, L1Entry, IsInL1, DT, PDT, DI))
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
      if (Dep && !Dep->isInput())
        return false;
    }
  return true;
}

bool isUnsafeToFuse(Loop &L1, Loop &L2, ScalarEvolution &SE, DependenceInfo &DI,
                    DominatorTree &DT, PostDominatorTree &PDT) {
  if (!checkLoop(L1) || !checkLoop(L2)) {
    errs() << "Loops don't have the right shape\n";
    return true;
  }

  if (L1.getLoopDepth() != L2.getLoopDepth()) {
    errs() << "Loops have different nesting level\n";
    return true;
  }

  // Make sure the two loops have constant trip counts
  const SCEV *TripCount1 = SE.getBackedgeTakenCount(&L1);
  const SCEV *TripCount2 = SE.getBackedgeTakenCount(&L2);
  if (isa<SCEVCouldNotCompute>(TripCount1) ||
      isa<SCEVCouldNotCompute>(TripCount2) || TripCount1 != TripCount2) {
    errs() << "Loops may have divergent trip count\n";
    return true;
  }

  Loop *L1Parent = L1.getParentLoop();
  Loop *L2Parent = L2.getParentLoop();
  // If L1 and L2 are nested inside other loops, those loops also need to be
  // fused
  if (!L1.isOutermost() && L1Parent != L2Parent) {
    if (isUnsafeToFuse(*L1.getParentLoop(), *L2.getParentLoop(), SE, DI, DT,
                       PDT)) {
      errs() << "Parent loops can't be fused\n";
      return true;
    }
    // TODO: maybe support convergent control flow?
    // For now, don't fuse nested loops that are conditionally executed
    // (since it's harder to prove they are executed together)
    if (!isControlFlowEquivalent(*L1.getParentLoop()->getHeader(),
                                 *getLoopEntry(L1), DT, PDT) ||
        !isControlFlowEquivalent(*L2.getParentLoop()->getHeader(),
                                 *getLoopEntry(L2), DT, PDT)) {
      errs() << "Can't fuse conditional nested loop\n";
      return true;
    }
  } else {
    if (!isControlFlowEquivalent(*L1.getLoopPreheader(), *L2.getLoopPreheader(),
                                 DT, PDT)) {
      errs() << "Loops are not control flow equivalent\n";
      return true;
    }

    bool OneBeforeTwo = DT.dominates(getLoopEntry(L1), getLoopEntry(L2));
    if ((OneBeforeTwo && !checkDependencies(L1, L2, DI, DT, PDT)) ||
        (!OneBeforeTwo && !checkDependencies(L2, L1, DI, DT, PDT))) {
      errs() << "Loops are dependent (memory)\n";
      return true;
    }
  }

  if (!L1.isLCSSAForm(DT) || !L2.isLCSSAForm(DT)) {
    errs() << "Loops are not in LCSSA\n";
    return true;
  }

  // Check if one loop computes any SSA values that are used by another loop
  for (PHINode &PN : L1.getExitBlock()->phis())
    if (isUsedByLoop(&PN, L2)) {
      errs() << "Loops are dependent (ssa)\n";
      return true;
    }
  for (PHINode &PN : L2.getExitBlock()->phis())
    if (isUsedByLoop(&PN, L1)) {
      errs() << "Loops are dependent (ssa)\n";
      return true;
    }

  return false; // *probably* safe
}

static void rewriteBranch(BasicBlock *Src, BasicBlock *OldDst,
                          BasicBlock *NewDst) {
  Src->getTerminator()->replaceUsesOfWith(OldDst, NewDst);
}

static bool getNumPHIs(BasicBlock *BB) {
  return std::distance(BB->phis().begin(), BB->phis().end());
}

bool fuseLoops(Loop &L1, Loop &L2, llvm::DominatorTree &DT,
               PostDominatorTree &PDT, llvm::DependenceInfo &DI) {
  BasicBlock *L1Preheader = L1.getLoopPreheader();
  BasicBlock *L2Preheader = L2.getLoopPreheader();
  BasicBlock *L1Header = L1.getHeader();
  BasicBlock *L2Header = L2.getHeader();
  BasicBlock *L1Latch = L1.getLoopLatch();
  BasicBlock *L2Latch = L2.getLoopLatch();
  BasicBlock *L1Exit = L1.getExitBlock();
  BasicBlock *L2Exit = L2.getExitBlock();

  LLVMContext &Ctx = L1Preheader->getContext();
  Function *F = L1Preheader->getParent();
  BasicBlock *L2Placeholder = BasicBlock::Create(Ctx, L2Preheader->getName()+".placeholder", F);
  BranchInst::Create(L2Exit /*to*/, L2Placeholder /*from*/);

  // TODO: get rid of this restriction
  if (getNumPHIs(L1Preheader) != 0 || getNumPHIs(L2Preheader) != 0)
    return false;

  // Rewrire all edges going into L2's preheader to, instead, go to
  // a dedicated placeholder for L2 that directly jumps to the L2's exit
  std::vector<BasicBlock *> Preds(pred_begin(L2Preheader),
                                  pred_end(L2Preheader));
  for (auto *BB : Preds)
    rewriteBranch(/*src=*/BB, /*old dst=*/L2Preheader,
                  /*new dst=*/L2Placeholder);

  // Run L2's preheader after L1's preheader
  rewriteBranch(/*src=*/L1Preheader, /*old dst=*/L1Header,
                /*new dst=*/L2Preheader);
  rewriteBranch(/*src=*/L2Preheader, /*old dst=*/L2Header,
                /*new dst=*/L1Header);

  // Run one iteration L2 after we are done with one iteration of L1
  ReplaceInstWithInst(L1Latch->getTerminator(), BranchInst::Create(L2Header));

  // hoist the PHI nodes in L2Header to L1Header
  while (auto *L2PHI = dyn_cast<PHINode>(&L2Header->front()))
    L2PHI->moveBefore(&*L1Header->getFirstInsertionPt());

  L1Header->replacePhiUsesWith(L1Preheader, L2Preheader);
  L1Header->replacePhiUsesWith(L1Latch, L2Latch);

  rewriteBranch(/*src=*/L2Latch, /*old dst=*/L2Header, /*new dst=*/L1Header);
  rewriteBranch(/*src=*/L2Latch, /*old dst=*/L2Exit, /*new dst=*/L1Exit);

  // Fix the PHIs contorlling the exit values
  L1Exit->replacePhiUsesWith(L1Latch, L2Latch);
  for (PHINode &PN : L2Exit->phis()) {
    auto ComesFromL2OrDominatesL1Exit = [&](BasicBlock *BB) {
      return BB == L2Latch || DT.dominates(PN.getIncomingValueForBlock(BB),
                                           L1Exit->getTerminator());
    };
    if (all_of(PN.blocks(), ComesFromL2OrDominatesL1Exit)) {
      PN.moveBefore(&*L1Exit->getFirstInsertionPt());
    } else {
      auto *Ty = PN.getType();
      SmallVector<BasicBlock *, 2> PredsOfL2Exit;
      PredsOfL2Exit.append(pred_begin(L1Exit), pred_end(L1Exit));
      auto *DummyPHI = PHINode::Create(Ty, PredsOfL2Exit.size(), "",
                                       &*L1Exit->getFirstInsertionPt());
      for (auto *BB : PredsOfL2Exit) {
        Value *V = (BB == L2Latch) ? PN.getIncomingValueForBlock(L2Latch)
                                   : UndefValue::get(Ty);
        DummyPHI->addIncoming(V, BB);
      }

      for (unsigned i = 0; i < PN.getNumIncomingValues(); i++) {
        auto *BB = PN.getIncomingBlock(i);
        if (BB == L2Latch) {
          PN.setIncomingValue(i, DummyPHI);
          PN.setIncomingBlock(i, L2Placeholder);
        }
      }
    }
  }

  return false;
}
