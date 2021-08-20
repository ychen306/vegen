#include "CodeMotionUtil.h"
#include "llvm/ADT/EquivalenceClasses.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/InitializePasses.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

namespace llvm {
void initializeTestCodeMotionPass(PassRegistry &);
}

namespace {

cl::list<std::string> InstGroups("inst-group",
                                 cl::desc("instructions to group together"));

cl::opt<bool> Gather("gather", cl::desc("use gatherInstructions"),
                     cl::init(false));

struct TestCodeMotion : public FunctionPass {
  static char ID;

  TestCodeMotion() : FunctionPass(ID) {
    initializeTestCodeMotionPass(*PassRegistry::getPassRegistry());
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

char TestCodeMotion::ID = 0;

bool TestCodeMotion::runOnFunction(Function &F) {
  auto &SE = getAnalysis<ScalarEvolutionWrapperPass>().getSE();
  auto &DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
  auto &PDT = getAnalysis<PostDominatorTreeWrapperPass>().getPostDomTree();
  auto &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
  auto &DI = getAnalysis<DependenceAnalysisWrapperPass>().getDI();

  StringMap<Instruction *> NameToInstMap;
  for (Instruction &I : instructions(F))
    NameToInstMap[I.getName()] = &I;
  if (InstGroups.empty())
    return false;

  EquivalenceClasses<Instruction *> CoupledInsts;
  for (StringRef IG : InstGroups) {
    SmallVector<StringRef> InstNames;
    IG.split(InstNames, ',');

    SmallVector<Instruction *> Insts;
    for (StringRef Name : InstNames) {
      auto *I = NameToInstMap.lookup(Name);
      if (!I)
        report_fatal_error("invalid inst group");
      Insts.push_back(I);
    }

    if (!Gather)
      for (auto *I : drop_begin(Insts))
        hoistTo(I, Insts.front()->getParent(), LI, SE, DT, PDT, DI,
                CoupledInsts);

    for (auto *I : drop_begin(Insts))
      CoupledInsts.unionSets(I, Insts.front());
  }

  if (Gather)
    gatherInstructions(&F, CoupledInsts, LI, DT, PDT, SE, DI);

  return true;
}

INITIALIZE_PASS_BEGIN(TestCodeMotion, "test-code-motion", "test-code-motion",
                      false, false)
INITIALIZE_PASS_DEPENDENCY(ScalarEvolutionWrapperPass)
INITIALIZE_PASS_DEPENDENCY(DependenceAnalysisWrapperPass)
INITIALIZE_PASS_DEPENDENCY(DominatorTreeWrapperPass)
INITIALIZE_PASS_DEPENDENCY(LoopInfoWrapperPass)
INITIALIZE_PASS_DEPENDENCY(PostDominatorTreeWrapperPass)
INITIALIZE_PASS_END(TestCodeMotion, "test-code-motion", "test-code-motion",
                    false, false)

static struct Register {
  Register() { initializeTestCodeMotionPass(*PassRegistry::getPassRegistry()); }
} X;
