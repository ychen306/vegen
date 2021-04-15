#include "InstSema.h"
#include "LocalDependenceAnalysis.h"
#include "MatchManager.h"
#include "Packer.h"
#include "Solver.h"
#include "Util.h"
#include "VectorPack.h"
#include "IRVec.h"
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

cl::opt<bool> AggressivePacking("aggressive", cl::desc("Turn on aggressive packing decisions"),
    cl::init(false));

static cl::opt<std::string>
    InstWrappersPath("inst-wrappers", cl::desc("Path to InstWrappers.bc"),
                     cl::Required);

static cl::opt<bool> UseMainlineSLP("use-slp", cl::desc("Use LLVM SLP"),
                                    cl::init(false));

///////// MCTS configs ///////////

static cl::opt<float> ParamC("c",
                             cl::desc("Specify the exploration factor (C)"),
                             cl::value_desc("C"), cl::init(0.25));

static cl::opt<float>
    ParamW("w", cl::desc("Specify the bias factor for the policy network (W)"),
                   cl::value_desc("W"), cl::init(100));

static cl::opt<unsigned>
    NumSimulations("simulations", cl::value_desc("Number of MCTS simulations"),
                   cl::init(10000));
//////////////////////////////////

static cl::opt<unsigned> EnumCap(
    "enum-cap",
    cl::desc("Cap the maximum number of packs enumerate for a instruction"),
    cl::value_desc("Enumeration cap"), cl::init(1000));

static cl::opt<unsigned> ExpandThreshold("expand-after",
                                         cl::value_desc("Expandsion threshold"),
                                         cl::init(9));

static cl::opt<unsigned> MaxNumLanes(
    "max-num-lanes",
    cl::desc(
        "Specify maximum number of lanes the vectorizer is allowed to pack"),
    cl::value_desc("Maximum number of lanes"), cl::init(8));

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

void vectorizeBasicBlock(BasicBlock &BB, VectorPackSet &Packs, Packer &Pkr,
                         PackingPolicy *Policy) {
  VectorPackSet PacksScratch = Packs;
  float BottomUpCost = optimizeBottomUp(PacksScratch, &Pkr, &BB);
  errs() << "Bottom-up cost: " << BottomUpCost << '\n';
  Packs = PacksScratch;
  return;
}

} // end anonymous namespace

char GSLP::ID = 0;

static SmallVector<Value *, 4> collectReductionElements(Instruction *I,
    std::vector<Instruction *> &Intermediates) {
  SmallVector<Value *, 4> Elems;

  std::vector<Value *> Worklist {I};
  DenseSet<Value *> Seen;

  while (!Worklist.empty()) {
    auto *V = Worklist.back();
    Worklist.pop_back();

    // if not an Add then found a leave
    Value *A, *B;
    if (!match(V, m_OneUse(m_Add(m_Value(A), m_Value(B))))) {
      Elems.push_back(V);
      continue;
    }

    // Abort if we try to detect a dag...
    // Only try to match for trees
    bool Inserted = Seen.insert(V).second;
    if (!Inserted)
      return {};

    if (V != I)
      Intermediates.push_back(cast<Instruction>(V));

    Worklist.push_back(A);
    Worklist.push_back(B);
  }
  return Elems;
}

// FIXME: propagate NSW and NUW
static Value *buildBalancedTree(IRBuilderBase &IRB, ArrayRef<Value *> Leaves) {
  if (Leaves.size() == 1)
    return Leaves[0];
  unsigned N = Leaves.size();
  auto *A = buildBalancedTree(IRB, Leaves.drop_back(N/2/*num drop*/));
  auto *B = buildBalancedTree(IRB, Leaves.slice(N-N/2/*num drop*/, N/2/*num keep*/));
  return IRB.CreateAdd(A, B);
}

static void balanceReductionTree(Function &F) {
  DenseSet<Instruction *> Ignore;
  for (auto &BB : F) {
    // Can't directly iterate over the BB that we are modifying
    std::vector<Instruction *> Worklist;
    for (auto &I : BB)
      Worklist.push_back(&I);

    while (!Worklist.empty()) {
      auto *I = Worklist.back();
      Worklist.pop_back();
      bool Inserted = Ignore.insert(I).second;
      if (!Inserted)
        continue;

      if (!match(I, m_Add(m_Value(), m_Value())))
        continue;

      std::vector<Instruction *> Intermediates;
      auto Elems = collectReductionElements(I, Intermediates);
      if (Elems.size() > 2) {
        IRBuilder<> IRB(I);
        auto *NewRoot = buildBalancedTree(IRB, Elems);
        I->replaceAllUsesWith(NewRoot);
        I->eraseFromParent();

        for (auto *I2 : Intermediates) {
          Ignore.insert(I2);
          I2->eraseFromParent();
        }

        //errs() << "MATCHED AND BALANCED REDUCTION : (\n";
        //for (auto *V : Elems)
        //  errs() << *V << '\n';
        //errs() << ")\n";
      }
    }
  }
}

bool GSLP::runOnFunction(Function &F) {
  //if (!F.getName().contains("dot"))
  //  return false;
  //if (!F.getName().contains("_Z5idct8PKsPs"))
  //  return false;
  ///if (!F.getName().contains("sbc"))
  //if (!F.getName().contains("fft8"))
  //  return false;
  //if (!F.getName().contains("interp"))
  //if (!F.getName().contains("idct8"))
  //if (!F.getName().contains("_Z5idct8PKsPs"))
  //if (!F.getName().contains("_Z5idct8PKsPs"))
  //if (!F.getName().contains("fft4"))
  //if (!F.getName().contains("fft4"))
  //if (!F.getName().contains("fft8"))
  //return false;
  //if (!F.getName().contains("idct"))
  //  return false;

  if (AggressivePacking)
    balanceReductionTree(F);
  errs() << F << '\n';
  // Table holding all IR vector instructions
  IRInstTable VecBindingTable;

  auto *AA = &getAnalysis<AAResultsWrapperPass>().getAAResults();
  auto *SE = &getAnalysis<ScalarEvolutionWrapperPass>().getSE();
  auto *TTI = &getAnalysis<TargetTransformInfoWrapperPass>().getTTI(F);
  auto *BFI = &getAnalysis<BlockFrequencyInfoWrapperPass>().getBFI();
  auto *DL = &F.getParent()->getDataLayout();

  std::vector<InstBinding *> SupportedIntrinsics;
  for (auto &Inst : Insts) {
    //if (Inst.getName().contains("hadd"))
    //  continue;
    if (Inst.getName().contains("hadd_ps"))
      continue;
    if (Inst.getName().contains("hsub_ps"))
      continue;
    if (isSupported(&Inst, F)) {
      SupportedIntrinsics.push_back(&Inst);
    }
  }
  for (auto *Inst : VecBindingTable.getBindings())
    SupportedIntrinsics.push_back(Inst);

  errs() << "~~~~ num supported intrinsics: " << SupportedIntrinsics.size() << '\n';
  Packer Pkr(SupportedIntrinsics, F, AA, DL, SE, TTI, BFI);
  VectorPackSet Packs(&F);
  for (auto &BB : F) {
    errs() << "Optimizing " << F.getName() << "/" << BB.getName() << '\n';
    vectorizeBasicBlock(BB, Packs, Pkr, nullptr);
  }

  IntrinsicBuilder Builder(*InstWrappers);
  errs() << "Generating vector code\n";
  Packs.codegen(Builder, Pkr);

  errs() << F << '\n';

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
  MPM.add(createSROAPass());
  MPM.add(createInstructionCombiningPass(true /*expensive combines*/));
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
