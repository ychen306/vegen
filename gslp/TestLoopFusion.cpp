#include "LoopFusion.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/BasicAliasAnalysis.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/Analysis/GlobalsModRef.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScopedNoAliasAA.h"
#include "llvm/Analysis/TypeBasedAliasAnalysis.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/InitializePasses.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils.h"

using namespace llvm;

namespace llvm {
void initializeTestLoopFusionPass(PassRegistry &);
}

namespace {

cl::opt<std::string>
    InputFileName(cl::Positional,
                  cl::desc("Specify the input llvm bitcode file"),
                  cl::value_desc("input file name"), cl::init("-"));
cl::opt<bool>
    DoFusion("do-fusion",
             cl::desc("Do fusion instead of testing whether it's safe to fuse"),
             cl::value_desc("run fuse safe-to-fuse loops"), cl::init(false));

cl::list<std::string> FusionGroups("fusion-group",
                                   cl::desc("group of loops to fuse"));

struct TestLoopFusion : public FunctionPass {
  static char ID;

  TestLoopFusion() : FunctionPass(ID) {
    initializeTestLoopFusionPass(*PassRegistry::getPassRegistry());
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<ScalarEvolutionWrapperPass>();
    AU.addRequired<DependenceAnalysisWrapperPass>();
    AU.addRequired<DominatorTreeWrapperPass>();
    AU.addRequired<LoopInfoWrapperPass>();
    AU.addRequired<PostDominatorTreeWrapperPass>();
  }

  bool runOnFunction(Function &) override;
};

} // namespace

char TestLoopFusion::ID = 0;

bool TestLoopFusion::runOnFunction(Function &F) {
  auto &SE = getAnalysis<ScalarEvolutionWrapperPass>().getSE();
  auto &DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
  auto &PDT = getAnalysis<PostDominatorTreeWrapperPass>().getPostDomTree();
  auto &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
  auto &DI = getAnalysis<DependenceAnalysisWrapperPass>().getDI();

  auto PrintFusionLegality = [&](Loop *L1, Loop *L2) {
    outs() << "Fusing " << L1->getHeader()->getName() << " and "
           << L2->getHeader()->getName() << " is ";
    if (isUnsafeToFuse(L1, L2, LI, SE, DI, DT, PDT) && !DoFusion)
      outs() << "unsafe\n";
    else
      outs() << "safe\n";
  };

  if (!FusionGroups.empty()) {
    StringMap<BasicBlock *> BlocksByName;
    for (auto &BB : F)
      BlocksByName[BB.getName()] = &BB;

    for (StringRef FG : FusionGroups) {
      SmallVector<StringRef> BlockNames;
      FG.split(BlockNames, ',');

      SmallVector<Loop *> Loops;
      for (StringRef Name : BlockNames) {
        assert(BlocksByName.lookup(Name));
        auto *BB = BlocksByName.lookup(Name);
        auto *L = LI.getLoopFor(BB);
        assert(L);
        Loops.push_back(L);
      }

      if (DoFusion) {
        for (unsigned i = 1; i < Loops.size(); i++) {
          if (Loop *Fused = fuseLoops(Loops[0], Loops[i], LI, DT, PDT, DI)) {
            Loops[0] = Fused;
          } else
            llvm_unreachable("failed to fuse fusable loops");
        }
      } else {
        for (unsigned i = 0; i < Loops.size(); i++)
          for (unsigned j = i + 1; j < Loops.size(); j++)
            PrintFusionLegality(Loops[i], Loops[j]);
      }
    }
    return DoFusion;
  }

  auto Loops = LI.getLoopsInPreorder();
  for (auto I = Loops.begin(), E = Loops.end(); I != E; ++I) {
    Loop *L1 = *I;
    if (!L1->isInnermost())
      continue;
    for (auto J = std::next(I); J != E; ++J) {
      Loop *L2 = *J;
      if (!L2->isInnermost())
        continue;

      if (DoFusion) {
        fuseLoops(L1, L2, LI, DT, PDT, DI);
        return true;
      }

      PrintFusionLegality(L1, L2);
    }
  }
  return false;
}

INITIALIZE_PASS_BEGIN(TestLoopFusion, "test-loop-fusion", "test-loop-fusion",
                      false, false)
INITIALIZE_PASS_DEPENDENCY(ScalarEvolutionWrapperPass)
INITIALIZE_PASS_DEPENDENCY(DependenceAnalysisWrapperPass)
INITIALIZE_PASS_DEPENDENCY(DominatorTreeWrapperPass)
INITIALIZE_PASS_DEPENDENCY(LoopInfoWrapperPass)
INITIALIZE_PASS_DEPENDENCY(PostDominatorTreeWrapperPass)
INITIALIZE_PASS_END(TestLoopFusion, "test-loop-fusion", "test-loop-fusion",
                    false, false)

int main(int argc, char **argv) {
  cl::ParseCommandLineOptions(argc, argv);

  LLVMContext Ctx;
  SMDiagnostic Err;
  std::unique_ptr<Module> M = parseIRFile(InputFileName, Err, Ctx);

  if (!M.get()) {
    Err.print(argv[0], errs());
    return 1;
  }

  legacy::PassManager Passes;

  // Add the alias analysis pipeline
  Passes.add(createTypeBasedAAWrapperPass());
  Passes.add(createScopedNoAliasAAWrapperPass());
  Passes.add(createGlobalsAAWrapperPass());
  Passes.add(createBasicAAWrapperPass());
  if (!DoFusion) {
    // Canonicalize the loops
    Passes.add(createLoopSimplifyPass());
    Passes.add(createLoopRotatePass());

    // Make isControlFlowEquivalent more precise
    Passes.add(createNewGVNPass());

    Passes.add(createLCSSAPass());
  }

  Passes.add(new TestLoopFusion());
  Passes.run(*M);

  if (DoFusion)
    outs() << *M << '\n';
}
