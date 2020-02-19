#include "InstSema.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Support/FormatVariadic.h"

using namespace llvm;
using namespace PatternMatch;

namespace {

class GSLP : public FunctionPass {
public:
  static char ID; // Pass identification, replacement for typeid
  GSLP() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override;
};

} // end anonymous namespace


// FIXME: this as some pretty significant performance problem.
// Solution: manually clone the instructions from the wrapper func.
// See https://stackoverflow.com/questions/43303943.
template <typename T, typename Inserter>
Value *InstBinding::create(
    IRBuilder<T, Inserter> &Builder,
    ArrayRef<Value *> Operands, unsigned char Imm8) const {
  std::string WrapperName = formatv("intrinsic_wrapper_{0}_{1}", Name, Imm8).str();
  auto *M = Builder.GetInsertBlock()->getModule();
  auto *F = M->getFunction(WrapperName);
  assert(F && "Intrinsic wrapper undefined.");
  return Builder.Create(F, Operands);
}

char GSLP::ID = 0;

bool GSLP::runOnFunction(Function &F) { return false; }

// Automatically enable the pass.
// http://adriansampson.net/blog/clangpass.html
static void registerGSLP(const PassManagerBuilder &,
                         legacy::PassManagerBase &PM) {
  PM.add(new GSLP());
}
static RegisterStandardPasses
    RegisterMyPass(PassManagerBuilder::EP_VectorizerStart, registerGSLP);
