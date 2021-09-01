#include "ConsecutiveCheck.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/InitializePasses.h"

using namespace llvm;

namespace llvm {
void initializeTestConsecutiveCheckPass(PassRegistry &);
}

namespace {
struct TestConsecutiveCheck : public FunctionPass {
  static char ID;

  TestConsecutiveCheck() : FunctionPass(ID) {
    initializeTestConsecutiveCheckPass(*PassRegistry::getPassRegistry());
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<ScalarEvolutionWrapperPass>();
    AU.addRequired<LoopInfoWrapperPass>();
  }

  bool runOnFunction(Function &) override;
};

} // namespace

char TestConsecutiveCheck::ID = 0;

bool TestConsecutiveCheck::runOnFunction(Function &F) {
  auto &SE = getAnalysis<ScalarEvolutionWrapperPass>().getSE();
  auto &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();

  const DataLayout &DL = F.getParent()->getDataLayout();
  for (auto &I : instructions(&F))
    for (auto &J : instructions(&F))
      if (isConsecutive(&I, &J, DL, SE, LI))
        errs() << I << " and " << J << " are consecutive\n";
  return false;
}

INITIALIZE_PASS_BEGIN(TestConsecutiveCheck, "test-consecutive-check", "test-consecutive-check",
                      false, false)
INITIALIZE_PASS_DEPENDENCY(ScalarEvolutionWrapperPass)
INITIALIZE_PASS_DEPENDENCY(LoopInfoWrapperPass)
INITIALIZE_PASS_END(TestConsecutiveCheck, "test-consecutive-check", "test-consecutive-check",
                    false, false)

static struct Register {
  Register() { initializeTestConsecutiveCheckPass(*PassRegistry::getPassRegistry()); }
} X;
