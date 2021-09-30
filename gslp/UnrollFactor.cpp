#include "UnrollFactor.h"
#include "LoopUnrolling.h"
#include "Packer.h"
#include "Solver.h"
#include "VectorPack.h"
#include "VectorPackContext.h"
#include "llvm/ADT/Triple.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/BasicAliasAnalysis.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/Analysis/GlobalsModRef.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/PhiValues.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScopedNoAliasAA.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/TypeBasedAliasAnalysis.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ScalarEvolutionExpander.h"
#include "llvm/Support/CommandLine.h"

using namespace llvm;

static cl::opt<bool> ForwardSeeds("forward-seeds", cl::desc("Forward seeds from the unroller"),
                                  cl::init(false));

namespace {
class AAResultsBuilder {
  std::function<const TargetLibraryInfo &(Function &F)> GetTLI;

  // BasicAA
  PhiValues PV;
  BasicAAResult BasicResult;

  ScopedNoAliasAAResult ScopedNoAliasResult;

  TypeBasedAAResult TBAAResult;

  // Globals AA
  CallGraph CG;
  GlobalsAAResult GlobalsResult;

  AAResults Result;

public:
  AAResultsBuilder(Module &M, Function &F,
                   std::function<const TargetLibraryInfo &(Function &F)> GetTLI,
                   AssumptionCache &AC, DominatorTree &DT, LoopInfo &LI)
      : GetTLI(GetTLI), PV(F),
        BasicResult(M.getDataLayout(), F, GetTLI(F), AC, &DT, &LI, &PV), CG(M),
        GlobalsResult(GlobalsAAResult::analyzeModule(M, GetTLI, CG)),
        Result(GetTLI(F)) {
    Result.addAAResult(BasicResult);
    Result.addAAResult(ScopedNoAliasResult);
    Result.addAAResult(TBAAResult);
    Result.addAAResult(GlobalsResult);
  }

  AAResults &getResult() { return Result; }
};

struct Range {
  bool Initialized;
  unsigned Lo, Hi; // inclusive
  Range() : Initialized(false) {}
  unsigned size() const { return Hi - Lo + 1; }
  void update(unsigned X) {
    if (!Initialized) {
      Lo = Hi = X;
      Initialized = true;
      return;
    }

    if (X < Lo)
      Lo = X;
    else if (X > Hi)
      Hi = X;
  }
};
raw_ostream &operator<<(raw_ostream &OS, const Range &R) {
  return OS << '[' << R.Lo << ',' << R.Hi << ']';
}

} // namespace

void unrollLoops(
    Function *F, ScalarEvolution &SE, LoopInfo &LI, AssumptionCache &AC,
    DominatorTree &DT, TargetTransformInfo *TTI,
    const DenseMap<Loop *, unsigned> &UFs,
    DenseMap<Loop *, UnrolledLoopTy> &DupToOrigLoopMap,
    DenseMap<Instruction *, UnrolledInstruction> *UnrolledIterations,
    DenseSet<BasicBlock *> *EpilogBlocks,
    EquivalenceClasses<BasicBlock *> *UnrolledBlocks) {

  auto GetOrigLoop = [&DupToOrigLoopMap](Loop *L) {
    auto It = DupToOrigLoopMap.find(L);
    if (It != DupToOrigLoopMap.end())
      return It->second.OrigLoop;
    return L;
  };

  SmallVector<Loop *, 8> Worklist;
  Worklist.assign(LI.begin(), LI.end());
  while (!Worklist.empty()) {
    Loop *L = Worklist.pop_back_val();

    unsigned UF = UFs.lookup(GetOrigLoop(L));
    if (UF <= 1) {
      Worklist.append(L->begin(), L->end());
      continue;
    }

    unsigned TripCount = SE.getSmallConstantMaxTripCount(L);
    if (TripCount && TripCount < UF)
      UF = TripCount;

    auto *ExitingBlock = L->getExitingBlock();
    UnrollLoopOptions ULO;
    ULO.TripCount = 0;
    ULO.Count = UF;
    ULO.Force = true;
    ULO.PeelCount = 0;
    ULO.TripMultiple = ExitingBlock ? SE.getSmallConstantTripMultiple(L, ExitingBlock) : 1;
    ULO.AllowRuntime = true;
    ULO.AllowExpensiveTripCount = true;
    ULO.ForgetAllSCEV = false;
    ULO.UnrollRemainder = false;
    ULO.PreserveOnlyFirst = false;
    ULO.PreserveCondBr = false;

    ValueMap<Value *, UnrolledValue> UnrollToOrigMap;
    Loop *EpilogL = nullptr;
    UnrollLoopWithVMap(L, ULO, &LI, &SE, &DT, &AC, TTI, true, UnrollToOrigMap,
                       &EpilogL);
    if (EpilogBlocks && EpilogL && EpilogL->getNumBlocks())
      EpilogBlocks->insert(EpilogL->block_begin(), EpilogL->block_end());

    // Map the cloned sub loops back to original loops
    for (auto KV : UnrollToOrigMap) {
      auto *BB = dyn_cast<BasicBlock>(KV.first);
      if (BB && UnrolledBlocks)
        UnrolledBlocks->unionSets(
            BB, const_cast<BasicBlock *>(cast<BasicBlock>(KV.second.V)));

      auto *NewLoop = LI.getLoopFor(BB);
      if (BB && UnrolledIterations) {
        for (auto &I : *BB) {
          auto It = UnrollToOrigMap.find(&I);
          if (It != UnrollToOrigMap.end() &&
              isa_and_nonnull<Instruction>(It->second.V)) {
            const Instruction *SrcI = cast<Instruction>(It->second.V);
            if (UnrolledIterations->count(SrcI))
              SrcI = UnrolledIterations->lookup(SrcI).OrigI;
            // If the loop of the unrolled block belongs to a loop different
            // to the one we start with, it means we are unrolling the outer loop,
            // which means that the inner unroll iter should be zero.
            unsigned InnerIter = NewLoop == L ? It->second.Iter : 0;
            UnrolledIterations->insert({&I, {SrcI, InnerIter}});
          }
        }
      }

      if (!BB || !LI.isLoopHeader(BB) || NewLoop == L)
        continue;
      auto *OrigBB = cast<BasicBlock>(KV.second.V);
      DupToOrigLoopMap.try_emplace(NewLoop, GetOrigLoop(LI.getLoopFor(OrigBB)),
                                   KV.second.Iter);
    }

    // Unroll the sub loops
    Worklist.append(L->begin(), L->end());
  }
}

std::vector<const OperandPack *>
getSeeds(Packer &Pkr, DenseMap<Loop *, UnrolledLoopTy> &DupToOrigLoopMap,
         DenseMap<Instruction *, UnrolledInstruction> &UnrolledIterations) {
  if (!ForwardSeeds)
    return {};

  auto &LI = Pkr.getLoopInfo();

  auto GetUnrollVector = [&](Instruction *I) {
    std::vector<unsigned> X;
    auto *BB = I->getParent();
    auto *L = LI.getLoopFor(BB);
    if (!L)
      return X;
    X.push_back(UnrolledIterations.count(I) ? UnrolledIterations.lookup(I).Iter
                                            : 0);
    for (; L; L = L->getParentLoop())
      X.push_back(DupToOrigLoopMap.count(L) ? DupToOrigLoopMap.lookup(L).Iter
                                            : 0);
    return X;
  };

  auto *F = Pkr.getFunction();

  // Mapping <an original instruction + its unroll vector> -> the unrolled
  // instruction
  DenseMap<const Instruction *, unsigned> InstToDim;
  std::map<std::pair<const Instruction *, std::vector<unsigned>>, Instruction *>
      UnrolledInsts;
  for (auto &I : instructions(F)) {
    auto It = UnrolledIterations.find(&I);
    if (It == UnrolledIterations.end())
      continue;
    auto *OrigI = It->second.OrigI;
    auto X = GetUnrollVector(&I);
    UnrolledInsts[{OrigI, X}] = &I;

    InstToDim[OrigI] = X.size();
  }

  unsigned MaxVecWidth = Pkr.getTTI()->getLoadStoreVecRegBitWidth(0);
  ReversePostOrderTraversal<Function *> RPO(F);
  auto *VPCtx = Pkr.getContext();
  std::vector<const OperandPack *> SeedOperands;
  for (auto *BB : RPO) {
    for (auto &I : reverse(*BB)) {
      auto *Ty = I.getType();
      if (Ty->isVoidTy() || Ty->isVectorTy())
        continue;
      unsigned MaxVL =
          MaxVecWidth / getBitWidth(&I, &F->getParent()->getDataLayout());

      auto It = UnrolledIterations.find(&I);
      bool IsUnrolled = It != UnrolledIterations.end();
      auto *OrigI = IsUnrolled ? It->second.OrigI : &I;
      const auto X = IsUnrolled
                         ? GetUnrollVector(&I)
                         : std::vector<unsigned>(InstToDim.lookup(&I), 0);

      for (unsigned Dim = 0; Dim < X.size(); Dim++) {
        // Try to find a chain along Dim
        auto X_scratch = X;
        SmallVector<Instruction *, 16> Chain{&I};
        while (Chain.size() < MaxVL) {
          ++X_scratch[Dim];
          auto It = UnrolledInsts.find({OrigI, X_scratch});
          if (It == UnrolledInsts.end())
            break;
          Chain.push_back(It->second);
        }
        if (Chain.size() > 1 && isPowerOf2_32(Chain.size())) {
          OperandPack OP;
          OP.assign(Chain.begin(), Chain.end());
          SeedOperands.push_back(VPCtx->getCanonicalOperandPack(OP));
        }

      }
    }
  }
  return SeedOperands;
}

static void refineUnrollFactors(Function *F, DominatorTree &DT, LoopInfo &LI,
                                ArrayRef<const InstBinding *> Insts,
                                LazyValueInfo *LVI, TargetTransformInfo *TTI,
                                BlockFrequencyInfo *BFI,
                                DenseMap<Loop *, unsigned> &UFs,
                                unsigned MaxUF = 8) {
  // Compute some analysis for the unroller
  Module *M = F->getParent();
  AssumptionCache AC(*F);
  TargetLibraryInfoWrapperPass TLIWrapper(Triple(M->getTargetTriple()));
  ScalarEvolution SE(*F, TLIWrapper.getTLI(*F), AC, DT, LI);

  DenseMap<Loop *, UnrolledLoopTy> DupToOrigLoopMap;
  // Mapping a basic block to its unrolled iteration
  DenseMap<Instruction *, UnrolledInstruction> UnrolledIterations;
  DenseSet<Loop *> OrigLoops;
  for (auto *L : LI.getLoopsInPreorder())
    OrigLoops.insert(L);

  auto GetOrigLoop = [&](Loop *L) {
    assert(OrigLoops.count(L) || DupToOrigLoopMap.count(L));
    return OrigLoops.count(L) ? L : DupToOrigLoopMap.lookup(L).OrigLoop;
  };

  // Unroll all the loops maximally
  DenseMap<Loop *, unsigned> MaxUFs = UFs;
  UFs.clear();
  DenseSet<BasicBlock *> EpilogBlocks;
  EquivalenceClasses<BasicBlock *> UnrolledBlocks;
  unrollLoops(F, SE, LI, AC, DT, TTI, MaxUFs, DupToOrigLoopMap,
              &UnrolledIterations, &EpilogBlocks, &UnrolledBlocks);

  // Re-do the alias analysis pipline
  auto GetTLI = [&TLIWrapper](Function &F) -> TargetLibraryInfo & {
    return TLIWrapper.getTLI(F);
  };
  AAResultsBuilder AABuilder(*M, *F, GetTLI, AC, DT, LI);
  AAResults &AA = AABuilder.getResult();
  DependenceInfo DI(F, &AA, &SE, &LI);

  // Wrap all the analysis in the packer
  PostDominatorTree PDT(*F);
  Packer Pkr(Insts, *F, &AA, &LI, &SE, &DT, &PDT, &DI, LVI, TTI, BFI,
             &UnrolledBlocks, false /*preplanning*/);

  auto SeedOperands = getSeeds(Pkr, DupToOrigLoopMap, UnrolledIterations);

  // Run the solver to find packs
  std::vector<const VectorPack *> Packs;
  optimizeBottomUp(Packs, &Pkr, SeedOperands, &EpilogBlocks);

  for (auto *VP : Packs) {
    SmallPtrSet<Instruction *, 32> Insts;
    VP->getPackedInstructions(Insts);

    std::map<Loop *, Range> PackedIterations;
    for (auto *I : Insts) {
      auto *BB = I->getParent();
      auto *L = LI.getLoopFor(BB);
      if (!L)
        continue;
      PackedIterations[L].update(
          UnrolledIterations.count(I) ? UnrolledIterations.lookup(I).Iter : 0);
      for (L = L->getParentLoop(); L; L = L->getParentLoop()) {
        PackedIterations[L].update(
            DupToOrigLoopMap.count(L) ? DupToOrigLoopMap.lookup(L).Iter : 0);
      }
    }
    for (const auto &LoopAndRange : PackedIterations) {
      Loop *L = LoopAndRange.first;
      const Range &R = LoopAndRange.second;

      // Ignore epilog loops
      if (!OrigLoops.count(L) && !DupToOrigLoopMap.count(L))
        continue;

      unsigned MinUF = R.size();
      if (R.Lo / MinUF != R.Hi / MinUF)
        MinUF *= 2;

      std::remove_reference<decltype(UFs)>::type::iterator It;
      bool Inserted;
      std::tie(It, Inserted) = UFs.try_emplace(GetOrigLoop(L), MinUF);
      if (!Inserted)
        It->second = std::max(It->second, MinUF);
    }
  }
}

void computeUnrollFactorImpl(ArrayRef<const InstBinding *> Insts,
                             LazyValueInfo *LVI, TargetTransformInfo *TTI,
                             BlockFrequencyInfo *BFI, Function *OrigF,
                             const LoopInfo &OrigLI,
                             DenseMap<Loop *, unsigned> &UFs) {
  ValueToValueMapTy VMap;
  Function *F = CloneFunction(OrigF, VMap);
  DominatorTree DT(*F);
  LoopInfo LI(DT);

  // Nothing to unroll
  if (LI.getTopLevelLoops().empty()) {
    F->eraseFromParent();
    return;
  }

  // Mapping the old loops to the cloned loops
  DenseMap<Loop *, unsigned> RefinedUnrollFactors;
  DenseMap<Loop *, Loop *> CloneToOrigMap;
  for (auto &OrigBB : *OrigF) {
    auto *BB = cast<BasicBlock>(VMap[&OrigBB]);
    Loop *OrigL = OrigLI.getLoopFor(&OrigBB);
    if (!OrigL)
      continue;
    Loop *L = LI.getLoopFor(BB);
    bool Inserted = CloneToOrigMap.try_emplace(L, OrigL).second;
    if (!Inserted)
      continue;
    if (unsigned UF = UFs.lookup(OrigL))
      RefinedUnrollFactors.try_emplace(L, UF);
  }

  refineUnrollFactors(F, DT, LI, Insts, LVI, TTI, BFI, RefinedUnrollFactors);

  UFs.clear();
  for (auto KV : RefinedUnrollFactors) {
    Loop *L = KV.first;
    unsigned UF = KV.second;
    assert(CloneToOrigMap.count(L));
    UFs.try_emplace(CloneToOrigMap.lookup(L), UF);
  }

  // Erase the clone after we are done
  F->eraseFromParent();
}

void computeUnrollFactor(ArrayRef<const InstBinding *> Insts,
                         LazyValueInfo *LVI, TargetTransformInfo *TTI,
                         BlockFrequencyInfo *BFI, Function *F,
                         const LoopInfo &LI, DenseMap<Loop *, unsigned> &UFs) {
  for (auto *L : const_cast<LoopInfo &>(LI).getLoopsInPreorder()) {
    UFs[L] = 8;
    computeUnrollFactorImpl(Insts, LVI, TTI, BFI, F, LI, UFs);
    errs() << "Unroll factor for loop " << L << "(depth=" << L->getLoopDepth()
           << ')' << " " << UFs.lookup(L) << '\n';
  }
  errs() << "========= final unroll plan ========\n";
  for (auto *L : const_cast<LoopInfo &>(LI).getLoopsInPreorder()) {
    errs() << "Unroll factor for loop " << L << "(depth=" << L->getLoopDepth()
           << ')' << " " << UFs.lookup(L) << '\n';
  }
}
