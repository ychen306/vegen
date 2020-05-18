#include "Policy.h"
//       ^^^^
//       this needs to be included first because torch pollutes global namespace
//       with "using namespace ..."
#include "IRVec.h"
#include "InstSema.h"
#include "LocalDependenceAnalysis.h"
#include "MatchManager.h"
#include "Packer.h"
#include "Solver.h"
#include "Util.h"
#include "VectorPack.h"
#include "VectorPackContext.h"
#include "VectorPackSet.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/Analysis/MemoryLocation.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/Analysis/VectorUtils.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/InitializePasses.h"
#include "llvm/Linker/Linker.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Timer.h"
#include "llvm/Support/raw_ostream.h"
// For pass building
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/InstCombine/InstCombine.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/InstSimplifyPass.h"
#include "llvm/Transforms/Vectorize.h"
#include <set>

using namespace llvm;
using namespace PatternMatch;

cl::opt<std::string> InstWrappersPath("inst-wrappers",
                                      cl::desc("Path to InstWrappers.bc"),
                                      cl::Required);
cl::opt<bool> UseMainlineSLP("use-slp", cl::desc("Use LLVM SLP"),
                             cl::init(false));

static cl::opt<std::string>
    ModelPath("model", cl::desc("Specify a file path for the trained model"),
              cl::value_desc("output model path"), cl::init("pack.pt"));

namespace llvm {
void initializeGSLPPass(PassRegistry &);
}

namespace {

class GSLP : public FunctionPass {
  std::unique_ptr<Module> InstWrappers;

public:
  static char ID; // Pass identification, replacement for typeid
  GSLP() : FunctionPass(ID) {
    initializeGSLPPass(*PassRegistry::getPassRegistry());
  }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<ScalarEvolutionWrapperPass>();
    AU.addRequired<AAResultsWrapperPass>();
    AU.addRequired<TargetTransformInfoWrapperPass>();
    AU.addRequired<BlockFrequencyInfoWrapperPass>();
  }

  bool runOnFunction(llvm::Function &) override;

  virtual bool doInitialization(Module &M) override {
    SMDiagnostic Err;
    errs() << "LOADING WRAPPERS\n";
    InstWrappers = parseIRFile(InstWrappersPath, Err, M.getContext());
    assert(InstWrappers && "Failed to parse Inst Wrappers");
    errs() << "WRAPPERS LOADED\n";

    return false;
  }
};

static IRInstTable VecBindingTable;

bool hasFeature(const llvm::Function &F, std::string Feature) {
  Attribute Features = F.getFnAttribute("target-features");
  return !Features.hasAttribute(Attribute::None) &&
         Features.getValueAsString().contains("+" + Feature);
}

bool isSupported(InstBinding *Inst, const llvm::Function &F) {
  for (auto &Feature : Inst->getTargetFeatures())
    if (!hasFeature(F, Feature))
      return false;
  return true;
}

} // end anonymous namespace

char GSLP::ID = 0;

bool GSLP::runOnFunction(llvm::Function &F) {
  IntrinsicBuilder Builder(*InstWrappers);
  // Packs.codegen(Builder, LDAs);

  assert(!verifyFunction(F, &errs()));
  return true;
}

INITIALIZE_PASS_BEGIN(GSLP, "gslp", "gslp", false, false)
INITIALIZE_PASS_DEPENDENCY(ScalarEvolutionWrapperPass)
INITIALIZE_PASS_DEPENDENCY(AAResultsWrapperPass)
INITIALIZE_PASS_DEPENDENCY(TargetTransformInfoWrapperPass)
INITIALIZE_PASS_DEPENDENCY(BlockFrequencyInfoWrapperPass)
INITIALIZE_PASS_END(GSLP, "gslp", "gslp", false, false)

// Automatically enable the pass.
// http://adriansampson.net/blog/clangpass.html
static void registerGSLP(const PassManagerBuilder &PMB,
                         legacy::PassManagerBase &MPM) {
  if (UseMainlineSLP) {
    errs() << "USING LLVM SLP\n";
    MPM.add(createSLPVectorizerPass());
  } else {
    errs() << "USING G-SLP\n";
    MPM.add(new GSLP());
  }

  // run the cleanup passes, copied from llvm's pass builder
  MPM.add(createInstructionCombiningPass(true /*expensive combines*/));
  MPM.add(createLoopUnrollPass(2 /*opt level*/, PMB.DisableUnrollLoops,
                               PMB.ForgetAllSCEVInLoopUnroll));
  if (!PMB.DisableUnrollLoops) {
    MPM.add(createInstructionCombiningPass(true /*expensive combines*/));
    MPM.add(
        createLICMPass(PMB.LicmMssaOptCap, PMB.LicmMssaNoAccForPromotionCap));
  }
  MPM.add(createAlignmentFromAssumptionsPass());
  MPM.add(createLoopSinkPass());
  MPM.add(createInstSimplifyLegacyPass());
  MPM.add(createDivRemPairsPass());
  MPM.add(createCFGSimplificationPass());
}

// Register this pass to run after all optimization,
// because we want this pass to replace LLVM SLP.
static RegisterStandardPasses
    RegisterMyPass(PassManagerBuilder::EP_OptimizerLast, registerGSLP);
