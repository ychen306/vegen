#include "LoopFusion.h"
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
#include "llvm/Transforms/Utils.h"
#include "llvm/Transforms/Scalar.h"

using namespace llvm;

cl::opt<std::string>
    InputFileName(cl::Positional,
                  cl::desc("Specify the input llvm bitcode file"),
                  cl::value_desc("input file name"), cl::init("-"));

namespace llvm {
void initializeTestLoopFusionPass(PassRegistry &);
}

namespace {

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

  for (auto I = LI.begin(), E = LI.end(); I != E; ++I) {
    Loop *L1 = *I;
    for (auto J = std::next(I); J != E; ++J) {
      Loop *L2 = *J;
      outs() << "Checking " << L1->getHeader()->getName() << " and "
             << L2->getHeader()->getName()
             << ", fusable: " << !isUnsafeToFuse(*L1, *L2, SE, DI, DT, PDT)
             << '\n';
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

  // Canonicalize the loops
  Passes.add(createLoopSimplifyPass());
  Passes.add(createLCSSAPass());
  Passes.add(createLoopRotatePass());

  Passes.add(new TestLoopFusion());
  Passes.run(*M);
}
