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

static cl::opt<std::string>
    InstWrappersPath("inst-wrappers", cl::desc("Path to InstWrappers.bc"),
                     cl::Required);
static cl::opt<bool> UseMainlineSLP("use-slp", cl::desc("Use LLVM SLP"),
                                    cl::init(false));

static cl::opt<std::string>
    ModelPath("model", cl::desc("Specify a file path for the trained model"),
              cl::value_desc("output model path"));

static cl::opt<bool> UseBottomUp("use-bottom-up",
                             cl::desc("Use the bottom up heuristics"),
                             cl::init(false));

static cl::opt<bool> UseMCTS("use-mcts",
                             cl::desc("Use tree search during optimization"),
                             cl::init(false));

static cl::opt<bool> NoPolicy("no-policy", cl::desc("Don't use the policy net"),
                              cl::init(false));

///////// MCTS configs ///////////
static cl::opt<unsigned> EmbSize("emb-size",
                                 cl::desc("Specify size of the embedding"),
                                 cl::value_desc("model embedding sizes"),
                                 cl::init(64));

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

////// Policy eval configs. /////////
static cl::opt<unsigned> NumPolicyThreads(
    "policy-threads",
    cl::value_desc("Number of threads used for policy evaluation"),
    cl::init(4));

static cl::opt<unsigned>
    PolicyBatchSize("policy-batch-size",
                    cl::value_desc("Batch size for policy evaluation"),
                    cl::init(8));

static cl::opt<unsigned>
    NumGNNLayers("num-gnn-layers",
                 cl::value_desc("Iterations of message passing"), cl::init(8));

static cl::opt<unsigned> MaxInflightPolicyRequests(
    "max-inflights",
    cl::value_desc("Maximum number of policy network evaluation requests"),
    cl::init(32));
/////////////////////////////////////

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
  if (UseBottomUp) {
    Packs = PacksScratch;
    return;
  }

  UCTNodeFactory Factory;
  RolloutEvaluator Evaluator;
  UCTSearch MCTS(ParamC, ParamW, EnumCap, ExpandThreshold, &Factory, &Pkr,
                 Policy, &Evaluator, Pkr.getTTI());
  PackEnumerationCache EnumCache;

  UCTNode *Root = Factory.getNode(std::make_unique<Frontier>(&BB, &Pkr));
  float TotalCost = 0;
  while (!Root->isTerminal()) {
    if (UseMCTS)
      MCTS.run(Root, NumSimulations);
    else
      Root->expand(MaxNumLanes, &Factory, Pkr.getTTI());

    assert(Root->expanded());

    auto &Transitions = Root->transitions();

    UCTNode::Transition *T;
    if (Transitions.size() == 1) {
      T = &*Transitions.begin();
    } else if (UseMCTS) {
      T = &*std::max_element(Transitions.begin(), Transitions.end(),

          [](const UCTNode::Transition &A, const UCTNode::Transition &B) {
              float ACost = -A.Cost - A.Next->minCost();
              float BCost = -B.Cost - B.Next->minCost();
            return std::tie(ACost, A.Count) < std::tie(BCost, B.Count);
          }
                              );
    } else {
      std::vector<float> Prob;
      Policy->predict(Root, Prob);
      auto It = std::max_element(Prob.begin(), Prob.end());
      T = &Transitions[It - Prob.begin()];
    }


    auto Node = Root;
    errs() << "====================================="
           << "\n\t t transition cost: " << T->transitionCost()
           << "\n\t num transitions: " << Transitions.size()
           << "\n\t scalar cost: " << Transitions.begin()->avgCost()
           << "\n\t t avg cost: " << T->avgCost()
           << "\n\t t->next avg cost: " << T->Next->avgCost()
           << "\n\t t->next min cost: " << T->Next->minCost()
           << "\n\t t->next terminal? " << T->Next->isTerminal()
           << "\n\t t visit count : " << T->visitCount()
           << "\n\t node visit count: " << Node->visitCount()
           << "\n\t min cost : " << Node->minCost()
           << "\n\t max cost : " << Node->maxCost()
           << "\n\t avg cost : " << Node->avgCost()
           << "\n\t num unresolved packs : "
           << Node->getFrontier()->getUnresolvedPacks().size()
           << "\n\t num unresolved scalars : "
           << Node->getFrontier()->numUnresolvedScalars() << '\n';

    if (T->VP) {
      errs() << "[MCTS] ADDING: " << *T->VP << '\n';
      Packs.tryAdd(T->VP);
    }
    Root = T->Next;
    TotalCost += T->transitionCost();
      errs() << "[MCTS} New cost: " << TotalCost << '\n';

  }
  // The MCTS queries the policy (if there's one) asynchronously,
  // cancel all requests if they haven't been processed yet.
  if (Policy)
    Policy->cancel();

  errs() << "Total cost: " << TotalCost << '\n';
}

} // end anonymous namespace

char GSLP::ID = 0;

bool GSLP::runOnFunction(llvm::Function &F) {
  // Table holding all IR vector instructions
  IRInstTable VecBindingTable;

  auto *AA = &getAnalysis<AAResultsWrapperPass>().getAAResults();
  auto *SE = &getAnalysis<ScalarEvolutionWrapperPass>().getSE();
  auto *TTI = &getAnalysis<TargetTransformInfoWrapperPass>().getTTI(F);
  auto *BFI = &getAnalysis<BlockFrequencyInfoWrapperPass>().getBFI();
  auto *DL = &F.getParent()->getDataLayout();

  torch::Device Device(torch::kCPU);
  if (torch::cuda::is_available())
    Device = torch::Device(torch::kCUDA);

  PackingModel Model(EmbSize, VecBindingTable.getBindings(), MaxNumLanes,
                     NumGNNLayers);
  if (ModelPath.getNumOccurrences()) {
    torch::load(Model, ModelPath, Device);
    errs() << "Model loaded\n";
  }

  Model->to(Device);
  Model->eval();
  NeuralPackingPolicy Policy(Model, Device, MaxInflightPolicyRequests,
                             PolicyBatchSize, NumPolicyThreads);

  errs() << "Built policy\n";
  //Packer Pkr(VecBindingTable.getBindings(), F, AA, DL, SE, TTI, BFI);
  std::vector<InstBinding *> SupportedIntrinsics;
  for (auto &Inst : Insts) {
    if (isSupported(&Inst, F)) {
      SupportedIntrinsics.push_back(&Inst);
    }
  }
  errs() << "~~~~ num supported intrinsics: " << SupportedIntrinsics.size() << '\n';
  Packer Pkr(SupportedIntrinsics, F, AA, DL, SE, TTI, BFI);
  //Packer Pkr(VecBindingTable.getBindings(), F, AA, DL, SE, TTI, BFI);
  VectorPackSet Packs(&F);
  for (auto &BB : F) {
    errs() << "Optimizing " << F.getName() << "/" << BB.getName() << '\n';
    vectorizeBasicBlock(BB, Packs, Pkr, NoPolicy ? nullptr : &Policy);
  }

  IntrinsicBuilder Builder(*InstWrappers);
  errs() << "Generating vector code\n";
  Packs.codegen(Builder, Pkr);

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
