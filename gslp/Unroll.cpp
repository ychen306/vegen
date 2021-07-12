#include "Unroll.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/Optional.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/Twine.h"
#include "llvm/ADT/ilist_iterator.h"
#include "llvm/ADT/iterator_range.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/DomTreeUpdater.h"
#include "llvm/Analysis/InstructionSimplify.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopIterator.h"
#include "llvm/Analysis/OptimizationRemarkEmitter.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/DiagnosticInfo.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Use.h"
#include "llvm/IR/User.h"
#include "llvm/IR/ValueHandle.h"
#include "llvm/IR/ValueMap.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/GenericDomTree.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/LoopPeel.h"
#include "llvm/Transforms/Utils/LoopSimplify.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Transforms/Utils/ScalarEvolutionExpander.h"
#include "llvm/Transforms/Utils/SimplifyIndVar.h"
#include "llvm/Transforms/Utils/UnrollLoop.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include <algorithm>
#include <assert.h>
#include <type_traits>
#include <vector>

using namespace llvm;

static cl::opt<bool>
    UnrollRuntimeEpilog("vegen-unroll-runtime-epilog", cl::init(false),
                        cl::Hidden,
                        cl::desc("Allow runtime unrolled loops to be unrolled "
                                 "with epilog instead of prolog."));

static bool needToInsertPhisForLCSSA(Loop *L,
                                     const std::vector<BasicBlock *> &Blocks,
                                     LoopInfo *LI) {
  for (BasicBlock *BB : Blocks) {
    if (LI->getLoopFor(BB) == L)
      continue;
    for (Instruction &I : *BB) {
      for (Use &U : I.operands()) {
        if (const auto *Def = dyn_cast<Instruction>(U)) {
          Loop *DefLoop = LI->getLoopFor(Def->getParent());
          if (!DefLoop)
            continue;
          if (DefLoop->contains(L))
            return true;
        }
      }
    }
  }
  return false;
}

void simplifyLoopAfterUnroll2(Loop *L, bool SimplifyIVs, LoopInfo *LI,
                              ScalarEvolution *SE, DominatorTree *DT,
                              AssumptionCache *AC,
                              const TargetTransformInfo *TTI) {
  // Simplify any new induction variables in the partially unrolled loop.
  if (SE && SimplifyIVs) {
    SmallVector<WeakTrackingVH, 16> DeadInsts;
    simplifyLoopIVs(L, SE, DT, LI, TTI, DeadInsts);

    // Aggressively clean up dead instructions that simplifyLoopIVs already
    // identified. Any remaining should be cleaned up below.
    while (!DeadInsts.empty()) {
      Value *V = DeadInsts.pop_back_val();
      if (Instruction *Inst = dyn_cast_or_null<Instruction>(V))
        RecursivelyDeleteTriviallyDeadInstructions(Inst);
    }
  }

  // At this point, the code is well formed.  We now do a quick sweep over the
  // inserted code, doing constant propagation and dead code elimination as we
  // go.
  const DataLayout &DL = L->getHeader()->getModule()->getDataLayout();
  for (BasicBlock *BB : L->getBlocks()) {
    for (BasicBlock::iterator I = BB->begin(), E = BB->end(); I != E;) {
      Instruction *Inst = &*I++;

      if (Value *V = SimplifyInstruction(Inst, {DL, nullptr, DT, AC}))
        if (LI->replacementPreservesLCSSAForm(Inst, V))
          Inst->replaceAllUsesWith(V);
      if (isInstructionTriviallyDead(Inst))
        BB->getInstList().erase(Inst);
    }
  }

  // TODO: after peeling or unrolling, previously loop variant conditions are
  // likely to fold to constants, eagerly propagating those here will require
  // fewer cleanup passes to be run.  Alternatively, a LoopEarlyCSE might be
  // appropriate.
}

static bool isEpilogProfitable(Loop *L) {
  BasicBlock *PreHeader = L->getLoopPreheader();
  BasicBlock *Header = L->getHeader();
  assert(PreHeader && Header);
  for (const PHINode &PN : Header->phis()) {
    if (isa<ConstantInt>(PN.getIncomingValueForBlock(PreHeader)))
      return true;
  }
  return false;
}

LoopUnrollResult
UnrollLoopWithVMap(Loop *L, UnrollLoopOptions ULO, LoopInfo *LI,
                   ScalarEvolution *SE, DominatorTree *DT, AssumptionCache *AC,
                   const TargetTransformInfo *TTI, bool PreserveLCSSA,
                   ValueMap<const Value *, UnrolledValue> &UnrollToOrigMap,
                   Loop **RemainderLoop) {

  if (!L->getLoopPreheader())
    return LoopUnrollResult::Unmodified;

  if (!L->getLoopLatch())
    return LoopUnrollResult::Unmodified;

  // Loops with indirectbr cannot be cloned.
  if (!L->isSafeToClone())
    return LoopUnrollResult::Unmodified;

  if (L->getHeader()->hasAddressTaken())
    return LoopUnrollResult::Unmodified;

  // Effectively "DCE" unrolled iterations that are beyond the tripcount
  // and will never be executed.
  if (ULO.TripCount != 0 && ULO.Count > ULO.TripCount)
    ULO.Count = ULO.TripCount;

  // Don't enter the unroll code if there is nothing to do.
  if (ULO.TripCount == 0 && ULO.Count < 2 && ULO.PeelCount == 0)
    return LoopUnrollResult::Unmodified;

  assert(ULO.Count > 0);
  assert(ULO.TripMultiple > 0);
  assert(ULO.TripCount == 0 || ULO.TripCount % ULO.TripMultiple == 0);

  // Are we eliminating the loop control altogether?
  bool CompletelyUnroll = ULO.Count == ULO.TripCount;

  // We assume a run-time trip count if the compiler cannot
  // figure out the loop trip count and the unroll-runtime
  // flag is specified.
  bool RuntimeTripCount =
      (ULO.TripCount == 0 && ULO.Count > 0 && ULO.AllowRuntime);

  assert((!RuntimeTripCount || !ULO.PeelCount) &&
         "Did not expect runtime trip-count unrolling "
         "and peeling for the same loop");

  bool Peeled = false;
  if (ULO.PeelCount) {
    Peeled = peelLoop(L, ULO.PeelCount, LI, SE, DT, AC, PreserveLCSSA);

    // Successful peeling may result in a change in the loop preheader/trip
    // counts. If we later unroll the loop, we want these to be updated.
    if (Peeled) {
      // According to our guards and profitability checks the only
      // meaningful exit should be latch block. Other exits go to deopt,
      // so we do not worry about them.
      BasicBlock *ExitingBlock = L->getLoopLatch();
      assert(ExitingBlock && "Loop without exiting block?");
      assert(L->isLoopExiting(ExitingBlock) && "Latch is not exiting?");
      ULO.TripCount = SE->getSmallConstantTripCount(L, ExitingBlock);
      ULO.TripMultiple = SE->getSmallConstantTripMultiple(L, ExitingBlock);
    }
  }

  // All these values should be taken only after peeling because they might have
  // changed.
  BasicBlock *Preheader = L->getLoopPreheader();
  BasicBlock *Header = L->getHeader();
  BasicBlock *LatchBlock = L->getLoopLatch();
  SmallVector<BasicBlock *, 4> ExitBlocks;
  L->getExitBlocks(ExitBlocks);
  std::vector<BasicBlock *> OriginalLoopBlocks = L->getBlocks();

  // Go through all exits of L and see if there are any phi-nodes there. We just
  // conservatively assume that they're inserted to preserve LCSSA form, which
  // means that complete unrolling might break this form. We need to either fix
  // it in-place after the transformation, or entirely rebuild LCSSA. TODO: For
  // now we just recompute LCSSA for the outer loop, but it should be possible
  // to fix it in-place.
  bool NeedToFixLCSSA = PreserveLCSSA && CompletelyUnroll &&
                        any_of(ExitBlocks, [](const BasicBlock *BB) {
                          return isa<PHINode>(BB->begin());
                        });

  // The current loop unroll pass can unroll loops that have
  // (1) single latch; and
  // (2a) latch is unconditional; or
  // (2b) latch is conditional and is an exiting block
  // FIXME: The implementation can be extended to work with more complicated
  // cases, e.g. loops with multiple latches.
  BranchInst *LatchBI = dyn_cast<BranchInst>(LatchBlock->getTerminator());

  // A conditional branch which exits the loop, which can be optimized to an
  // unconditional branch in the unrolled loop in some cases.
  BranchInst *ExitingBI = nullptr;
  bool LatchIsExiting = L->isLoopExiting(LatchBlock);
  if (LatchIsExiting)
    ExitingBI = LatchBI;
  else if (BasicBlock *ExitingBlock = L->getExitingBlock())
    ExitingBI = dyn_cast<BranchInst>(ExitingBlock->getTerminator());
  if (!LatchBI || (LatchBI->isConditional() && !LatchIsExiting)) {
    // If the peeling guard is changed this assert may be relaxed or even
    // deleted.
    assert(!Peeled && "Peeling guard changed!");
    return LoopUnrollResult::Unmodified;
  }

  // Loops containing convergent instructions must have a count that divides
  // their TripMultiple.
  bool EpilogProfitability = UnrollRuntimeEpilog.getNumOccurrences()
                                 ? UnrollRuntimeEpilog
                                 : isEpilogProfitable(L);

  if (RuntimeTripCount && ULO.TripMultiple % ULO.Count != 0 &&
      !UnrollRuntimeLoopRemainder(L, ULO.Count, ULO.AllowExpensiveTripCount,
                                  EpilogProfitability, ULO.UnrollRemainder,
                                  ULO.ForgetAllSCEV, LI, SE, DT, AC, TTI,
                                  PreserveLCSSA, RemainderLoop)) {
    if (ULO.Force)
      RuntimeTripCount = false;
    else {
      return LoopUnrollResult::Unmodified;
    }
  }

  // If we know the trip count, we know the multiple...
  unsigned BreakoutTrip = 0;
  if (ULO.TripCount != 0) {
    BreakoutTrip = ULO.TripCount % ULO.Count;
    ULO.TripMultiple = 0;
  } else {
    // Figure out what multiple to use.
    BreakoutTrip = ULO.TripMultiple =
        (unsigned)GreatestCommonDivisor64(ULO.Count, ULO.TripMultiple);
  }

  // We are going to make changes to this loop. SCEV may be keeping cached info
  // about it, in particular about backedge taken count. The changes we make
  // are guaranteed to invalidate this information for our loop. It is tempting
  // to only invalidate the loop being unrolled, but it is incorrect as long as
  // all exiting branches from all inner loops have impact on the outer loops,
  // and if something changes inside them then any of outer loops may also
  // change. When we forget outermost loop, we also forget all contained loops
  // and this is what we need here.
  if (SE) {
    if (ULO.ForgetAllSCEV)
      SE->forgetAllLoops();
    else
      SE->forgetTopmostLoop(L);
  }

  Optional<bool> ContinueOnTrue = None;
  BasicBlock *LoopExit = nullptr;
  if (ExitingBI) {
    ContinueOnTrue = L->contains(ExitingBI->getSuccessor(0));
    LoopExit = ExitingBI->getSuccessor(*ContinueOnTrue);
  }

  // For the first iteration of the loop, we should use the precloned values for
  // PHI nodes.  Insert associations now.
  ValueToValueMapTy LastValueMap;
  std::vector<PHINode *> OrigPHINode;
  for (BasicBlock::iterator I = Header->begin(); isa<PHINode>(I); ++I) {
    OrigPHINode.push_back(cast<PHINode>(I));
  }

  std::vector<BasicBlock *> Headers;
  std::vector<BasicBlock *> ExitingBlocks;
  std::vector<BasicBlock *> ExitingSucc;
  std::vector<BasicBlock *> Latches;
  Headers.push_back(Header);
  Latches.push_back(LatchBlock);
  if (ExitingBI) {
    ExitingBlocks.push_back(ExitingBI->getParent());
    ExitingSucc.push_back(ExitingBI->getSuccessor(!(*ContinueOnTrue)));
  }

  // The current on-the-fly SSA update requires blocks to be processed in
  // reverse postorder so that LastValueMap contains the correct value at each
  // exit.
  LoopBlocksDFS DFS(L);
  DFS.perform(LI);

  // Stash the DFS iterators before adding blocks to the loop.
  LoopBlocksDFS::RPOIterator BlockBegin = DFS.beginRPO();
  LoopBlocksDFS::RPOIterator BlockEnd = DFS.endRPO();

  std::vector<BasicBlock *> UnrolledLoopBlocks = L->getBlocks();

  // Loop Unrolling might create new loops. While we do preserve LoopInfo, we
  // might break loop-simplified form for these loops (as they, e.g., would
  // share the same exit blocks). We'll keep track of loops for which we can
  // break this so that later we can re-simplify them.
  SmallSetVector<Loop *, 4> LoopsToSimplify;
  for (Loop *SubLoop : *L)
    LoopsToSimplify.insert(SubLoop);

  if (Header->getParent()->isDebugInfoForProfiling())
    for (BasicBlock *BB : L->getBlocks())
      for (Instruction &I : *BB)
        if (!isa<DbgInfoIntrinsic>(&I))
          if (const DILocation *DIL = I.getDebugLoc()) {
            auto NewDIL = DIL->cloneByMultiplyingDuplicationFactor(ULO.Count);
            if (NewDIL)
              I.setDebugLoc(NewDIL.getValue());
          }

  // Identify what noalias metadata is inside the loop: if it is inside the
  // loop, the associated metadata must be cloned for each iteration.
  SmallVector<MDNode *, 6> LoopLocalNoAliasDeclScopes;
  identifyNoAliasScopesToClone(L->getBlocks(), LoopLocalNoAliasDeclScopes);

  SmallVector<Instruction *> PHIReplacements;

  for (unsigned It = 1; It != ULO.Count; ++It) {
    SmallVector<BasicBlock *, 8> NewBlocks;
    SmallDenseMap<const Loop *, Loop *, 4> NewLoops;
    NewLoops[L] = L;

    for (LoopBlocksDFS::RPOIterator BB = BlockBegin; BB != BlockEnd; ++BB) {
      ValueToValueMapTy VMap;
      BasicBlock *New = CloneBasicBlock(*BB, VMap, "." + Twine(It));
      Header->getParent()->getBasicBlockList().push_back(New);

      assert((*BB != Header || LI->getLoopFor(*BB) == L) &&
             "Header should not be in a sub-loop");
      // Tell LI about New.
      const Loop *OldLoop = addClonedBlockToLoopInfo(*BB, New, LI, NewLoops);
      if (OldLoop)
        LoopsToSimplify.insert(NewLoops[OldLoop]);

      if (*BB == Header)
        // Loop over all of the PHI nodes in the block, changing them to use
        // the incoming values from the previous block.
        for (PHINode *OrigPHI : OrigPHINode) {
          PHINode *NewPHI = cast<PHINode>(VMap[OrigPHI]);
          Value *InVal = NewPHI->getIncomingValueForBlock(LatchBlock);
          if (Instruction *InValI = dyn_cast<Instruction>(InVal))
            if (It > 1 && L->contains(InValI))
              InVal = LastValueMap[InValI];
          VMap[OrigPHI] = InVal;
          if (auto *I = dyn_cast<Instruction>(InVal))
            PHIReplacements.push_back(I);
          New->getInstList().erase(NewPHI);
        }

      // Update our running map of newest clones
      LastValueMap[*BB] = New;
      for (ValueToValueMapTy::iterator VI = VMap.begin(), VE = VMap.end();
           VI != VE; ++VI) {
        LastValueMap[VI->first] = VI->second;
        UnrollToOrigMap[VI->second] = UnrolledValue{It, VI->first};
      }

      // Add phi entries for newly created values to all exit blocks.
      for (BasicBlock *Succ : successors(*BB)) {
        if (L->contains(Succ))
          continue;
        for (PHINode &PHI : Succ->phis()) {
          Value *Incoming = PHI.getIncomingValueForBlock(*BB);
          ValueToValueMapTy::iterator It = LastValueMap.find(Incoming);
          if (It != LastValueMap.end())
            Incoming = It->second;
          PHI.addIncoming(Incoming, New);
        }
      }
      // Keep track of new headers and latches as we create them, so that
      // we can insert the proper branches later.
      if (*BB == Header)
        Headers.push_back(New);
      if (*BB == LatchBlock)
        Latches.push_back(New);

      // Keep track of the exiting block and its successor block contained in
      // the loop for the current iteration.
      if (ExitingBI) {
        if (*BB == ExitingBlocks[0])
          ExitingBlocks.push_back(New);
        if (*BB == ExitingSucc[0])
          ExitingSucc.push_back(New);
      }

      NewBlocks.push_back(New);
      UnrolledLoopBlocks.push_back(New);

      // Update DomTree: since we just copy the loop body, and each copy has a
      // dedicated entry block (copy of the header block), this header's copy
      // dominates all copied blocks. That means, dominance relations in the
      // copied body are the same as in the original body.
      if (DT) {
        if (*BB == Header)
          DT->addNewBlock(New, Latches[It - 1]);
        else {
          auto BBDomNode = DT->getNode(*BB);
          auto BBIDom = BBDomNode->getIDom();
          BasicBlock *OriginalBBIDom = BBIDom->getBlock();
          DT->addNewBlock(
              New, cast<BasicBlock>(LastValueMap[cast<Value>(OriginalBBIDom)]));
        }
      }
    }

    // Remap all instructions in the most recent iteration
    remapInstructionsInBlocks(NewBlocks, LastValueMap);
    for (BasicBlock *NewBlock : NewBlocks) {
      for (Instruction &I : *NewBlock) {
        if (auto *II = dyn_cast<IntrinsicInst>(&I))
          if (II->getIntrinsicID() == Intrinsic::assume)
            AC->registerAssumption(II);
      }
    }

    {
      // Identify what other metadata depends on the cloned version. After
      // cloning, replace the metadata with the corrected version for both
      // memory instructions and noalias intrinsics.
      std::string ext = (Twine("It") + Twine(It)).str();
      cloneAndAdaptNoAliasScopes(LoopLocalNoAliasDeclScopes, NewBlocks,
                                 Header->getContext(), ext);
    }
  }

  // Loop over the PHI nodes in the original block, setting incoming values.
  for (PHINode *PN : OrigPHINode) {
    if (CompletelyUnroll) {
      PN->replaceAllUsesWith(PN->getIncomingValueForBlock(Preheader));
      Header->getInstList().erase(PN);
    } else if (ULO.Count > 1) {
      Value *InVal = PN->removeIncomingValue(LatchBlock, false);
      // If this value was defined in the loop, take the value defined by the
      // last iteration of the loop.
      if (Instruction *InValI = dyn_cast<Instruction>(InVal)) {
        if (L->contains(InValI))
          InVal = LastValueMap[InVal];
      }
      assert(Latches.back() == LastValueMap[LatchBlock] && "bad last latch");
      PN->addIncoming(InVal, Latches.back());
    }
  }

  auto setDest = [](BasicBlock *Src, BasicBlock *Dest, BasicBlock *BlockInLoop,
                    bool NeedConditional, Optional<bool> ContinueOnTrue,
                    bool IsDestLoopExit) {
    auto *Term = cast<BranchInst>(Src->getTerminator());
    if (NeedConditional) {
      // Update the conditional branch's successor for the following
      // iteration.
      assert(ContinueOnTrue.hasValue() &&
             "Expecting valid ContinueOnTrue when NeedConditional is true");
      Term->setSuccessor(!(*ContinueOnTrue), Dest);
    } else {
      // Remove phi operands at this loop exit
      if (!IsDestLoopExit) {
        BasicBlock *BB = Src;
        for (BasicBlock *Succ : successors(BB)) {
          // Preserve the incoming value from BB if we are jumping to the block
          // in the current loop.
          if (Succ == BlockInLoop)
            continue;
          for (PHINode &Phi : Succ->phis())
            Phi.removeIncomingValue(BB, false);
        }
      }
      // Replace the conditional branch with an unconditional one.
      BranchInst::Create(Dest, Term);
      Term->eraseFromParent();
    }
  };

  // Connect latches of the unrolled iterations to the headers of the next
  // iteration. If the latch is also the exiting block, the conditional branch
  // may have to be preserved.
  for (unsigned i = 0, e = Latches.size(); i != e; ++i) {
    // The branch destination.
    unsigned j = (i + 1) % e;
    BasicBlock *Dest = Headers[j];
    bool NeedConditional = LatchIsExiting;

    if (LatchIsExiting) {
      if (RuntimeTripCount && j != 0)
        NeedConditional = false;

      // For a complete unroll, make the last iteration end with a branch
      // to the exit block.
      if (CompletelyUnroll) {
        if (j == 0)
          Dest = LoopExit;
        // If using trip count upper bound to completely unroll, we need to
        // keep the conditional branch except the last one because the loop
        // may exit after any iteration.
        assert(NeedConditional &&
               "NeedCondition cannot be modified by both complete "
               "unrolling and runtime unrolling");
        NeedConditional =
            (ULO.PreserveCondBr && j && !(ULO.PreserveOnlyFirst && i != 0));
      } else if (j != BreakoutTrip &&
                 (ULO.TripMultiple == 0 || j % ULO.TripMultiple != 0)) {
        // If we know the trip count or a multiple of it, we can safely use an
        // unconditional branch for some iterations.
        NeedConditional = false;
      }
    }

    setDest(Latches[i], Dest, Headers[i], NeedConditional, ContinueOnTrue,
            Dest == LoopExit);
  }

  if (!LatchIsExiting) {
    // If the latch is not exiting, we may be able to simplify the conditional
    // branches in the unrolled exiting blocks.
    for (unsigned i = 0, e = ExitingBlocks.size(); i != e; ++i) {
      // The branch destination.
      unsigned j = (i + 1) % e;
      bool NeedConditional = true;

      if (RuntimeTripCount && j != 0)
        NeedConditional = false;

      if (CompletelyUnroll)
        // We cannot drop the conditional branch for the last condition, as we
        // may have to execute the loop body depending on the condition.
        NeedConditional = j == 0 || ULO.PreserveCondBr;
      else if (j != BreakoutTrip &&
               (ULO.TripMultiple == 0 || j % ULO.TripMultiple != 0))
        // If we know the trip count or a multiple of it, we can safely use an
        // unconditional branch for some iterations.
        NeedConditional = false;

      // Conditional branches from non-latch exiting block have successors
      // either in the same loop iteration or outside the loop. The branches are
      // already correct.
      if (NeedConditional)
        continue;
      setDest(ExitingBlocks[i], ExitingSucc[i], ExitingSucc[i], NeedConditional,
              None, false);
    }

    // When completely unrolling, the last latch becomes unreachable.
    if (CompletelyUnroll) {
      BranchInst *Term = cast<BranchInst>(Latches.back()->getTerminator());
      new UnreachableInst(Term->getContext(), Term);
      Term->eraseFromParent();
    }
  }

  // Update dominators of blocks we might reach through exits.
  // Immediate dominator of such block might change, because we add more
  // routes which can lead to the exit: we can now reach it from the copied
  // iterations too.
  if (DT && ULO.Count > 1) {
    for (auto *BB : OriginalLoopBlocks) {
      auto *BBDomNode = DT->getNode(BB);
      SmallVector<BasicBlock *, 16> ChildrenToUpdate;
      for (auto *ChildDomNode : BBDomNode->children()) {
        auto *ChildBB = ChildDomNode->getBlock();
        if (!L->contains(ChildBB))
          ChildrenToUpdate.push_back(ChildBB);
      }
      BasicBlock *NewIDom;
      if (ExitingBI && BB == ExitingBlocks[0]) {
        // The latch is special because we emit unconditional branches in
        // some cases where the original loop contained a conditional branch.
        // Since the latch is always at the bottom of the loop, if the latch
        // dominated an exit before unrolling, the new dominator of that exit
        // must also be a latch.  Specifically, the dominator is the first
        // latch which ends in a conditional branch, or the last latch if
        // there is no such latch.
        // For loops exiting from non latch exiting block, we limit the
        // branch simplification to single exiting block loops.
        NewIDom = ExitingBlocks.back();
        for (unsigned i = 0, e = ExitingBlocks.size(); i != e; ++i) {
          Instruction *Term = ExitingBlocks[i]->getTerminator();
          if (isa<BranchInst>(Term) &&
              cast<BranchInst>(Term)->isConditional()) {
            NewIDom =
                DT->findNearestCommonDominator(ExitingBlocks[i], Latches[i]);
            break;
          }
        }
      } else {
        // The new idom of the block will be the nearest common dominator
        // of all copies of the previous idom. This is equivalent to the
        // nearest common dominator of the previous idom and the first latch,
        // which dominates all copies of the previous idom.
        NewIDom = DT->findNearestCommonDominator(BB, LatchBlock);
      }
      for (auto *ChildBB : ChildrenToUpdate)
        DT->changeImmediateDominator(ChildBB, NewIDom);
    }
  }

  Optional<DomTreeUpdater> DTU;
  if (DT)
    DTU.emplace(DT, DomTreeUpdater::UpdateStrategy::Lazy);
  // Merge adjacent basic blocks, if possible.
  for (BasicBlock *Latch : Latches) {
    BranchInst *Term = dyn_cast<BranchInst>(Latch->getTerminator());
    assert((Term ||
            (CompletelyUnroll && !LatchIsExiting && Latch == Latches.back())) &&
           "Need a branch as terminator, except when fully unrolling with "
           "unconditional latch");
    if (Term && Term->isUnconditional()) {
      BasicBlock *Dest = Term->getSuccessor(0);
      BasicBlock *Fold = Dest->getUniquePredecessor();
      if (MergeBlockIntoPredecessor(Dest, DTU ? DTU.getPointer() : nullptr,
                                    LI)) {
        // Dest has been folded into Fold. Update our worklists accordingly.
        std::replace(Latches.begin(), Latches.end(), Dest, Fold);
        llvm::erase_value(UnrolledLoopBlocks, Dest);
      }
    }
  }
  // Apply updates to the DomTree.
  if (DT)
    DT = &DTU->getDomTree();

  {
    auto &DL = L->getHeader()->getModule()->getDataLayout();
    SCEVExpander Expander(*SE, DL, "unroller");
    // Simplify the values that *used to be* computed by PHIs
    for (Instruction *I : PHIReplacements)
      if (SE->isSCEVable(I->getType())) {
        auto *I2 = Expander.expandCodeFor(SE->getSCEV(I), I->getType(), I);
        assert(UnrollToOrigMap.count(I));
        UnrollToOrigMap[I2] = UnrollToOrigMap[I];
        UnrollToOrigMap.erase(I);
        I->replaceAllUsesWith(I2);
        I->eraseFromParent();
      }
  } // Scope for scev expander

  // At this point, the code is well formed.  We now simplify the unrolled loop,
  // doing constant propagation and dead code elimination as we go.
  simplifyLoopAfterUnroll2(L, !CompletelyUnroll && (ULO.Count > 1 || Peeled),
                           LI, SE, DT, AC, TTI);

  Loop *OuterL = L->getParentLoop();
  // Update LoopInfo if the loop is completely removed.
  if (CompletelyUnroll)
    LI->erase(L);

  // After complete unrolling most of the blocks should be contained in OuterL.
  // However, some of them might happen to be out of OuterL (e.g. if they
  // precede a loop exit). In this case we might need to insert PHI nodes in
  // order to preserve LCSSA form.
  // We don't need to check this if we already know that we need to fix LCSSA
  // form.
  // TODO: For now we just recompute LCSSA for the outer loop in this case, but
  // it should be possible to fix it in-place.
  if (PreserveLCSSA && OuterL && CompletelyUnroll && !NeedToFixLCSSA)
    NeedToFixLCSSA |=
        ::needToInsertPhisForLCSSA(OuterL, UnrolledLoopBlocks, LI);

  // If we have a pass and a DominatorTree we should re-simplify impacted loops
  // to ensure subsequent analyses can rely on this form. We want to simplify
  // at least one layer outside of the loop that was unrolled so that any
  // changes to the parent loop exposed by the unrolling are considered.
  if (DT) {
    if (OuterL) {
      // OuterL includes all loops for which we can break loop-simplify, so
      // it's sufficient to simplify only it (it'll recursively simplify inner
      // loops too).
      if (NeedToFixLCSSA) {
        // LCSSA must be performed on the outermost affected loop. The unrolled
        // loop's last loop latch is guaranteed to be in the outermost loop
        // after LoopInfo's been updated by LoopInfo::erase.
        Loop *LatchLoop = LI->getLoopFor(Latches.back());
        Loop *FixLCSSALoop = OuterL;
        if (!FixLCSSALoop->contains(LatchLoop))
          while (FixLCSSALoop->getParentLoop() != LatchLoop)
            FixLCSSALoop = FixLCSSALoop->getParentLoop();

        formLCSSARecursively(*FixLCSSALoop, *DT, LI, SE);
      } else if (PreserveLCSSA) {
        assert(OuterL->isLCSSAForm(*DT) &&
               "Loops should be in LCSSA form after loop-unroll.");
      }

      // TODO: That potentially might be compile-time expensive. We should try
      // to fix the loop-simplified form incrementally.
      simplifyLoop(OuterL, DT, LI, SE, AC, nullptr, PreserveLCSSA);
    } else {
      // Simplify loops for which we might've broken loop-simplify form.
      for (Loop *SubLoop : LoopsToSimplify)
        simplifyLoop(SubLoop, DT, LI, SE, AC, nullptr, PreserveLCSSA);
    }
  }

  return CompletelyUnroll ? LoopUnrollResult::FullyUnrolled
                          : LoopUnrollResult::PartiallyUnrolled;
}
