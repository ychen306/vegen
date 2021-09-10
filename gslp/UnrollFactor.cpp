#include "UnrollFactor.h"
#include "LoopUnrolling.h"
#include "Packer.h"
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

using namespace llvm;

static Function *clone(const Function *F, ValueToValueMapTy &VMap) {
  auto FCopy = Function::Create(F->getFunctionType(), F->getLinkage(),
                                F->getAddressSpace());

  for (auto Pair : zip(F->args(), FCopy->args()))
    VMap[&std::get<0>(Pair)] = &std::get<1>(Pair);

  SmallVector<ReturnInst *> Returns;
  CloneFunctionInto(FCopy, F, VMap, false /*module level change*/, Returns);
  return FCopy;
}

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
} // namespace

static void computeUnrollFactorImpl(Packer *Pkr, Function *F,
                                    DenseMap<Loop *, unsigned> &UFs) {}

void computeUnrollFactor(Packer *OrigPkr, const Function *OrigF,
                         const LoopInfo &OrigLI,
                         DenseMap<const Loop *, unsigned> &UFs) {
  ValueToValueMapTy VMap;
  Function *F = clone(OrigF, VMap);

  Module *M = const_cast<Module *>(OrigF->getParent());

  // (Re)build the analysis for the clone
  TargetLibraryInfoWrapperPass TLIWrapper(Triple(M->getTargetTriple()));
  DominatorTree DT(*F);
  PostDominatorTree PDT(*F);
  LoopInfo LI(DT);
  AssumptionCache AC(*F);
  ScalarEvolution SE(*F, TLIWrapper.getTLI(*F), AC, DT, LI);
  // LazyValueInfo is fully lazy, so we can reuse it.
  auto *LVI = &OrigPkr->getLVI();

  // Re-do the alias analysis pipline for the cloned funtion
  auto GetTLI = [&TLIWrapper](Function &F) { return TLIWrapper.getTLI(F); };
  AAResultsBuilder AABuilder(*M, *F, GetTLI, AC, DT, LI);
  AAResults &AA = AABuilder.getResult();
  DependenceInfo DI(F, &AA, &SE, &LI);

  // Wrap all the analysis in the packer
  Packer Pkr(OrigPkr->getInsts(), *F, &AA, &LI, &SE, &DT, &PDT, &DI, LVI,
             OrigPkr->getTTI(), OrigPkr->getBFI());

  // Mapping the old loops to the cloned loops
  DenseMap<const Loop *, Loop *> LoopMap;
  for (auto &OrigBB : *OrigF) {
    auto *BB = cast<BasicBlock>(VMap[&OrigBB]);
    Loop *OrigL = OrigLI.getLoopFor(&OrigBB);
    Loop *L = LI.getLoopFor(BB);
    LoopMap.try_emplace(OrigL, L);
  }

  // Now compute the unrolling factor on the cloned function, which we are free
  // to modify
  DenseMap<Loop *, unsigned> UnrollFactors;
  computeUnrollFactorImpl(&Pkr, F, UnrollFactors);

  for (auto KV : UnrollFactors) {
    Loop *L = KV.first;
    unsigned UF = KV.second;
    assert(LoopMap.count(L));
    UFs.try_emplace(LoopMap.lookup(L), UF);
  }
}
