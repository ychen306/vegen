#include "LoopFusion.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/ScopedNoAliasAA.h"
#include "llvm/Analysis/TypeBasedAliasAnalysis.h"
#include "llvm/Analysis/GlobalsModRef.h"
#include "llvm/Analysis/BasicAliasAnalysis.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/InitializePasses.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"

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

char TestLoopFusion::ID;

bool TestLoopFusion::runOnFunction(Function &F) {
  auto &SE = getAnalysis<ScalarEvolutionWrapperPass>(F).getSE();
  auto &DT = getAnalysis<DominatorTreeWrapperPass>(F).getDomTree();
  auto &PDT = getAnalysis<PostDominatorTreeWrapperPass>(F).getPostDomTree();
  auto &LI = getAnalysis<LoopInfoWrapperPass>(F).getLoopInfo();
  auto &DI = getAnalysis<DependenceAnalysisWrapperPass>(F).getDI();
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

  // Add the alias analysis pipeline
  legacy::PassManager Passes;
  Passes.add(createTypeBasedAAWrapperPass());
  Passes.add(createScopedNoAliasAAWrapperPass());
  Passes.add(createGlobalsAAWrapperPass());
  Passes.add(createBasicAAWrapperPass());
  Passes.add(new TestLoopFusion());
  Passes.run(*M);
}
