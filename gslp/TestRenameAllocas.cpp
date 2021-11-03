#include "RenameAllocas.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/IR/Dominators.h"
#include "llvm/InitializePasses.h"

using namespace llvm;

namespace llvm {
void initializeAllocaRenamerPass(PassRegistry &);
}

namespace {

// For testing, otherweise we just call renameAllocas directly
struct AllocaRenamer : public FunctionPass {
  static char ID;
  AllocaRenamer() : FunctionPass(ID) {
    initializeAllocaRenamerPass(*PassRegistry::getPassRegistry());
  }
  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<AAResultsWrapperPass>();
    AU.addRequired<LoopInfoWrapperPass>();
    AU.addRequired<DominatorTreeWrapperPass>();
    AU.addRequired<PostDominatorTreeWrapperPass>();
  }

  bool runOnFunction(Function &F) override {
    auto &DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
    auto &PDT = getAnalysis<PostDominatorTreeWrapperPass>().getPostDomTree();
    auto &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
    auto &AA = getAnalysis<AAResultsWrapperPass>().getAAResults();

    SmallVector<AllocaInst *> Allocas;
    for (auto &I : F.getEntryBlock())
      if (auto *Alloca = dyn_cast<AllocaInst>(&I))
        Allocas.push_back(Alloca);

    renameAllocas(DT, PDT, LI, AA, F.getParent()->getDataLayout(), Allocas);
    return true;
  }
};

} // namespace

char AllocaRenamer::ID = 0;

INITIALIZE_PASS_BEGIN(AllocaRenamer, "rename-allocas", "rename-allocas", false,
                      false)
INITIALIZE_PASS_DEPENDENCY(AAResultsWrapperPass)
INITIALIZE_PASS_DEPENDENCY(LoopInfoWrapperPass)
INITIALIZE_PASS_DEPENDENCY(PostDominatorTreeWrapperPass)
INITIALIZE_PASS_DEPENDENCY(DominatorTreeWrapperPass)
INITIALIZE_PASS_END(AllocaRenamer, "rename-allocas", "rename-allocas", false,
                    false)

static struct Register {
  Register() { initializeAllocaRenamerPass(*PassRegistry::getPassRegistry()); }
} X;
