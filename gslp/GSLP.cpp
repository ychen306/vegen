#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/PatternMatch.h"

using namespace llvm;
using namespace PatternMatch;

#include "rules.inc"

namespace {

class GSLP : public FunctionPass {
public:
  static char ID; // Pass identification, replacement for typeid
  GSLP() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override;
};

} // end anonymous namespace

char GSLP::ID = 0;

bool GSLP::runOnFunction(Function &F) {
  return false;
}

// Automatically enable the pass.
// http://adriansampson.net/blog/clangpass.html
static void registerGSLP(const PassManagerBuilder &,
                         legacy::PassManagerBase &PM) {
  PM.add(new GSLP());
}
static RegisterStandardPasses
  RegisterMyPass(PassManagerBuilder::EP_VectorizerStart,
                 registerGSLP);
