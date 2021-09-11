#include "UnrollFactor.h"
#include "LoopUnrolling.h"
#include "Packer.h"
#include "Solver.h"
#include "VectorPackContext.h"
#include "VectorPack.h"
#include "llvm/ADT/Triple.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/BasicAliasAnalysis.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/Analysis/GlobalsModRef.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/PhiValues.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScopedNoAliasAA.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/TypeBasedAliasAnalysis.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ScalarEvolutionExpander.h"

using namespace llvm;

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

class UnrollInfo {
  struct UnrollRecord {
    Loop *L;
    unsigned Iter; // < UF
    UnrollRecord(Loop *L, unsigned Iter = 0) : L(L), Iter(Iter) {}
  };

  std::map<const Instruction *, SmallVector<UnrollRecord, 4>> InstToRecords;

public:
  UnrollInfo(Function *F, LoopInfo &LI);
  // `Unrolled` is the `Iter`'th version of Orig after unrolling `L`
  void trackUnrolledInst(const Instruction *Orig, const Instruction *Unrolled,
                         Loop *L, unsigned Iter);
};

} // namespace

UnrollInfo::UnrollInfo(Function *F, LoopInfo &LI) {
  for (auto &BB : *F) {
    SmallVector<Loop *> LoopNest;
    for (auto *L = LI.getLoopFor(&BB); L; L = L->getParentLoop())
      LoopNest.push_back(L);
    for (auto &I : BB)
      for (auto *L : reverse(LoopNest))
        InstToRecords[&I].emplace_back(L);
  }
}

void UnrollInfo::trackUnrolledInst(const Instruction *Orig,
                                   const Instruction *Unrolled, Loop *L,
                                   unsigned Iter) {
  if (InstToRecords.count(Orig))
    return;
  assert(!InstToRecords.count(Unrolled));
  auto &Records = InstToRecords[Unrolled] = InstToRecords[Orig];
  for (auto &Record : Records)
    if (Record.L == L) {
      Record.Iter = Iter;
      break;
    }
}

static void
computeUnrollFactorImpl(Function *F, DominatorTree &DT, LoopInfo &LI,
                        ArrayRef<const InstBinding *> Insts, LazyValueInfo *LVI,
                        TargetTransformInfo *TTI, BlockFrequencyInfo *BFI,
                        DenseMap<Loop *, unsigned> &UFs, unsigned MaxUF = 2) {
  // Compute some analysis for the unroller
  Module *M = F->getParent();
  AssumptionCache AC(*F);
  TargetLibraryInfoWrapperPass TLIWrapper(Triple(M->getTargetTriple()));
  ScalarEvolution SE(*F, TLIWrapper.getTLI(*F), AC, DT, LI);

  // Unroll *all* loops
  UnrollInfo UI(F, LI);
  auto LoopsInPreorder = LI.getLoopsInPreorder();
  for (Loop *L : reverse(LoopsInPreorder)) {
    unsigned UF = MaxUF;
    unsigned TripCount = SE.getSmallConstantMaxTripCount(L);
    if (TripCount && TripCount < UF)
      UF = TripCount;

    UnrollLoopOptions ULO;
    ULO.TripCount = 0;
    ULO.Count = UF;
    ULO.Force = true;
    ULO.PeelCount = 0;
    ULO.TripMultiple = SE.getSmallConstantTripMultiple(L);
    ULO.AllowRuntime = true;
    ULO.AllowExpensiveTripCount = true;
    ULO.ForgetAllSCEV = false;
    ULO.UnrollRemainder = false;
    ULO.PreserveOnlyFirst = false;
    ULO.PreserveCondBr = false;

    bool PreserveLCSSA = L->isLCSSAForm(DT);

    ValueMap<const Value *, UnrolledValue> UnrollToOrigMap;
    UnrollLoopWithVMap(L, ULO, &LI, &SE, &DT, &AC, TTI, PreserveLCSSA,
                       UnrollToOrigMap, nullptr /*remainder loop*/);
    for (const auto &KV : UnrollToOrigMap) {
      unsigned Iter = KV.second.Iter;
      assert(Iter > 0);
      const Value *OrigV = KV.second.V;
      auto *OrigI = dyn_cast<Instruction>(OrigV);
      if (!OrigI)
        continue;
      auto *I = cast<Instruction>(KV.first);
      UI.trackUnrolledInst(OrigI, I, L, Iter);
    }
  }

  // Re-do the alias analysis pipline
  auto GetTLI = [&TLIWrapper](Function &F) { return TLIWrapper.getTLI(F); };
  AAResultsBuilder AABuilder(*M, *F, GetTLI, AC, DT, LI);
  AAResults &AA = AABuilder.getResult();
  DependenceInfo DI(F, &AA, &SE, &LI);

  // Wrap all the analysis in the packer
  PostDominatorTree PDT(*F);
  Packer Pkr(Insts, *F, &AA, &LI, &SE, &DT, &PDT, &DI, LVI, TTI, BFI);

  // Run the solver to find packs
  std::vector<const VectorPack *> Packs;
  optimizeBottomUp(Packs, &Pkr);
  for (auto *VP : Packs)
    errs() << *VP << '\n';
}

void computeUnrollFactor(Packer *Pkr, Function *OrigF, const LoopInfo &OrigLI,
                         DenseMap<const Loop *, unsigned> &UFs) {
  ValueToValueMapTy VMap;
  Function *F = CloneFunction(OrigF, VMap);
  DominatorTree DT(*F);
  LoopInfo LI(DT);

  // Mapping the old loops to the cloned loops
  DenseMap<const Loop *, Loop *> LoopMap;
  for (auto &OrigBB : *OrigF) {
    auto *BB = cast<BasicBlock>(VMap[&OrigBB]);
    Loop *OrigL = OrigLI.getLoopFor(&OrigBB);
    if (!OrigL)
      continue;
    Loop *L = LI.getLoopFor(BB);
    LoopMap.try_emplace(OrigL, L);
  }

  // Now compute the unrolling factor on the cloned function, which we are free
  // to modify
  DenseMap<Loop *, unsigned> UnrollFactors;
  computeUnrollFactorImpl(F, DT, LI, Pkr->getInsts(), &Pkr->getLVI(), Pkr->getTTI(),
                          Pkr->getBFI(), UnrollFactors);

  for (auto KV : UnrollFactors) {
    Loop *L = KV.first;
    unsigned UF = KV.second;
    assert(LoopMap.count(L));
    UFs.try_emplace(LoopMap.lookup(L), UF);
  }

  // Erase the clone after we are done
  F->eraseFromParent();
}
