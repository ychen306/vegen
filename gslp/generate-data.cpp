#include "IRModel.h"
#include "IRVec.h"
#include "Packer.h"
#include "Policy.h"
#include "Serialize.h"
#include "Solver.h"
#include "SupervisionGenerator.h"
#include "llvm/ADT/Triple.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScopedNoAliasAA.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/Analysis/TypeBasedAliasAnalysis.h"
#include "llvm/CodeGen/CommandFlags.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/GlobPattern.h"
#include "llvm/Support/Host.h"
#include "llvm/Support/TargetRegistry.h"
#include "llvm/Support/ThreadLocal.h"
#include "llvm/Support/ThreadPool.h"
#include "llvm/Support/Timer.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/TargetSelect.h"

using namespace llvm;

static cl::opt<std::string>
    TrainDir(cl::Positional,
             cl::desc("Specify a train directory of bitcode files"),
             cl::value_desc("train directory"), cl::Required);

static cl::opt<std::string>
    ModelPath("model", cl::desc("Specify a file path to the model"),
              cl::value_desc("model path"), cl::init(""));

static cl::opt<std::string>
    TargetTriple("mtriple", cl::desc("Override target triple for module"));

static cl::opt<unsigned> EmbSize("emb-size",
                                 cl::desc("Specify size of the embedding"),
                                 cl::value_desc("model embedding sizes"),
                                 cl::init(64));

static cl::opt<unsigned> MaxNumLanes(
    "max-num-lanes",
    cl::desc(
        "Specify maximum number of lanes the vectorizer is allowed to pack"),
    cl::value_desc("Maximum number of lanes"), cl::init(8));

static cl::opt<std::string> ArchivePath(
    "o",
    cl::desc(
        "Specify the output directory where will archive the sampled data"),
    cl::value_desc("Output directory"), cl::init("decision-archive"));

static cl::opt<unsigned> ArchiveBlockSize("archive-block-size",
                                          cl::value_desc("Archive block size"),
                                          cl::init(50));

static cl::opt<float> ParamC("c",
                             cl::desc("Specify the exploration factor (C)"),
                             cl::value_desc("C"), cl::init(0.25));

static cl::opt<float>
    ParamW("w", cl::desc("Specify the bias factor for the policy network (W)"),
           cl::value_desc("W"), cl::init(100));

static cl::opt<unsigned> SamplesPerBlock(
    "samples",
    cl::desc("Specify the number of decisions we sample when dumping "
             "optimizing decisions of a basic block"),
    cl::value_desc("Number of decisions to sample per basic block"),
    cl::init(20));

static cl::opt<unsigned>
    NumSimulations("simulations", cl::value_desc("Number of MCTS simulations"),
                   cl::init(10000));

static cl::opt<unsigned> EnumCap(
    "enum-cap",
    cl::desc("Cap the maximum number of packs enumerate for a instruction"),
    cl::value_desc("Enumeration cap"), cl::init(1000));

static cl::opt<unsigned> ExpandThreshold("expand-after",
                                         cl::value_desc("Expandsion threshold"),
                                         cl::init(9));

static cl::opt<unsigned>
    NumThreads("threads", cl::desc("Number of threads to use"), cl::init(4));

static cl::opt<unsigned> NumPolicyThreads(
    "policy-threads",
    cl::value_desc("Number of threads used for policy evaluation"),
    cl::init(4));

static cl::opt<unsigned>
    PolicyBatchSize("policy-batch-size",
                    cl::value_desc("Batch size for policy evaluation"),
                    cl::init(8));

static cl::opt<unsigned> NumGNNLayers("num-gnn-layers",
                                      cl::value_desc("Number of GNN layers"),
                                      cl::init(8));

static cl::opt<unsigned> MaxInflightPolicyRequests(
    "max-inflights",
    cl::value_desc("Maximum number of policy network evaluation requests"),
    cl::init(32));

static codegen::RegisterCodeGenFlags CGF;

namespace llvm {
void initializeGeneratorWrapperPass(PassRegistry &);
}

namespace {
// An nop pass we run to collect Packers, which requires many other analyses
class GeneratorWrapper : public FunctionPass {
public:
  static char ID; // Pass identification, replacement for typeid
  static std::unique_ptr<SupervisionGenerator> SG;
  // Allocate a distinct device to each main search thread if possible
  static torch::Device Device;
  static PackingModel Model;
  static sys::ThreadLocal<PackingPolicy> Policy;
  static std::unique_ptr<TargetMachine> TM;
  std::string FuncName;
  int BBId;

  GeneratorWrapper() : FunctionPass(ID), BBId(-1) {
    initializeGeneratorWrapperPass(*PassRegistry::getPassRegistry());
  }
  GeneratorWrapper(std::string FuncName, int BBId)
      : FunctionPass(ID), FuncName(FuncName), BBId(BBId) {}

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<ScalarEvolutionWrapperPass>();
    AU.addRequired<AAResultsWrapperPass>();
    AU.addRequired<TargetTransformInfoWrapperPass>();
    AU.addRequired<BlockFrequencyInfoWrapperPass>();
  }
  bool runOnFunction(llvm::Function &) override;
};

} // namespace

static IRInstTable VecBindingTable;

static void runGeneratorOnBasicBlock(std::string ModulePath,
                                     std::string FuncName, int BBId) {
  LLVMContext Ctx;
  SMDiagnostic Diag;
  std::unique_ptr<Module> M = parseIRFile(ModulePath, Diag, Ctx);
  if (!M)
    Diag.print("Trainer failed to load bitcode:", errs());

  // Add the alias analysis pipeline
  legacy::PassManager Passes;
  Passes.add(createTypeBasedAAWrapperPass());
  Passes.add(createScopedNoAliasAAWrapperPass());
  Passes.add(createGlobalsAAWrapperPass());
  Passes.add(createBasicAAWrapperPass());
  Passes.add(new GeneratorWrapper(FuncName, BBId));
  Passes.run(*M);
}

bool GeneratorWrapper::runOnFunction(llvm::Function &F) {
  auto *AA = &getAnalysis<AAResultsWrapperPass>().getAAResults();
  auto *SE = &getAnalysis<ScalarEvolutionWrapperPass>().getSE();
  auto *BFI = &getAnalysis<BlockFrequencyInfoWrapperPass>().getBFI();

  auto TTI = TM->getTargetTransformInfo(F);

  assert(BBId != -1);

  auto *DL = &F.getParent()->getDataLayout();

  if (F.getName() != FuncName)
    return false;

  // Find the basic block we want to run the generator on.
  BasicBlock *TargetBB = nullptr;
  int i = 0;
  for (auto &BB : F)
    if (i++ == BBId) {
      TargetBB = &BB;
      break;
    }

  Packer Pkr(VecBindingTable.getBindings(), F, AA, DL, SE, &TTI, BFI);
  if (ModelPath.getNumOccurrences()) {
    // Initialize the thread local policy.
    if (!Policy.get()) {
      Policy.set(new NeuralPackingPolicy(Model, Device,
                                         MaxInflightPolicyRequests,
                                         PolicyBatchSize, NumPolicyThreads));
    }
  }
  SG->run(Policy.get(), &Pkr, TargetBB);
  return false;
}

std::unique_ptr<SupervisionGenerator> GeneratorWrapper::SG;
// FIXME: we need to create a distribute the model on a pool of GPU devices.
torch::Device GeneratorWrapper::Device(torch::kCPU);
PackingModel GeneratorWrapper::Model = nullptr;
sys::ThreadLocal<PackingPolicy> GeneratorWrapper::Policy;
std::unique_ptr<TargetMachine> GeneratorWrapper::TM;

char GeneratorWrapper::ID = 0;

INITIALIZE_PASS_BEGIN(GeneratorWrapper, "pic", "pic", false, false)
INITIALIZE_PASS_DEPENDENCY(ScalarEvolutionWrapperPass)
INITIALIZE_PASS_DEPENDENCY(AAResultsWrapperPass)
INITIALIZE_PASS_DEPENDENCY(TargetTransformInfoWrapperPass)
INITIALIZE_PASS_DEPENDENCY(BlockFrequencyInfoWrapperPass)
INITIALIZE_PASS_END(GeneratorWrapper, "pic", "pic", false, false)

static std::unique_ptr<TargetMachine> createTargetMachine() {
  Triple TheTriple(Triple::normalize(TargetTriple));
  if (TheTriple.getTriple().empty() || !TargetTriple.getNumOccurrences())
    TheTriple.setTriple(sys::getDefaultTargetTriple());

  std::string Error;
  const Target *TheTarget =
      TargetRegistry::lookupTarget(codegen::getMArch(), TheTriple, Error);
  if (!TheTarget) {
    errs() << "Failed to build target machine: " << Error << '\n';
    exit(1);
  }

  std::string CPUStr = codegen::getCPUStr();
  std::string FeaturesStr = codegen::getFeaturesStr();
  TargetOptions Options = codegen::InitTargetOptionsFromCodeGenFlags();
  Optional<Reloc::Model> RM = codegen::getExplicitRelocModel();

  return std::unique_ptr<TargetMachine>(TheTarget->createTargetMachine(
      TheTriple.getTriple(), CPUStr, FeaturesStr, Options, RM,
      codegen::getExplicitCodeModel(), CodeGenOpt::Aggressive));
}

int main(int argc, char **argv) {
  cl::ParseCommandLineOptions(argc, argv);

  InitializeAllTargets();
  InitializeAllTargetMCs();

  GeneratorWrapper::TM = createTargetMachine();

  errs() << "Num vector insts: " << VecBindingTable.getBindings().size()
         << '\n';

  std::error_code EC;
  ExitOnError ExitOnErr("Error: ");
  auto CheckError = [&]() { ExitOnErr(errorCodeToError(EC)); };

  torch::NoGradGuard Guard;

  EC = sys::fs::create_directory(ArchivePath);
  CheckError();

  PackingModel Model(EmbSize, VecBindingTable.getBindings(), MaxNumLanes,
                     NumGNNLayers);

  torch::Device Device(torch::kCPU);
  if (torch::cuda::is_available())
    Device = torch::Device(torch::kCUDA);

  // If we are running the MCTS with a model...
  if (ModelPath.getNumOccurrences())
    torch::load(Model, ModelPath, Device);

  Model->to(Device);
  Model->eval();

  GeneratorWrapper::Device = Device;
  GeneratorWrapper::Model = Model;

  PolicyArchiver Archiver(ArchiveBlockSize, ArchivePath);
  RolloutEvaluator Evaluator;
  GeneratorWrapper::SG.reset(new SupervisionGenerator(
      Archiver, &Evaluator, Model, EnumCap, ExpandThreshold, SamplesPerBlock,
      ParamC, ParamW, NumSimulations));

  ThreadPool Threads(hardware_concurrency(NumThreads));

  // Add the alias analysis pipeline
  legacy::PassManager Passes;
  Passes.add(createTypeBasedAAWrapperPass());
  Passes.add(createScopedNoAliasAAWrapperPass());
  Passes.add(createGlobalsAAWrapperPass());
  Passes.add(createBasicAAWrapperPass());
  Passes.add(new GeneratorWrapper());

  sys::fs::directory_iterator DirEnd;
  sys::fs::directory_iterator DirIt(TrainDir, EC);
  CheckError();

  Expected<GlobPattern> BCPatOrErr = GlobPattern::create("*.bc");
  if (BCPatOrErr)
    ExitOnErr(BCPatOrErr.takeError());
  auto &BCPat = BCPatOrErr.get();

  LLVMContext Ctx;

  std::vector<std::string> ModulePaths;
  for (;;) {
    if (DirIt == DirEnd)
      break;

    std::string FilePath = DirIt->path();
    if (BCPat.match(FilePath))
      ModulePaths.push_back(FilePath);

    DirIt.increment(EC);
    CheckError();
  }

  std::mutex StatLock;
  std::condition_variable StatCond;
  std::atomic<int64_t> NumProcessedBlocks(0);

  unsigned NumBlocks = 0;
  unsigned Scanned = 0;
  for (auto &FilePath : ModulePaths) {
    SMDiagnostic Diag;
    errs() << "\rScanning modules: " << ++Scanned << "/" << ModulePaths.size();
    std::unique_ptr<Module> M = parseIRFile(FilePath, Diag, Ctx);
    if (!M)
      Diag.print("Trainer failed to load bitcode:", errs());
    else {

      for (auto &F : *M) {
        if (F.getName() != "adi")
          continue;
        for (unsigned i = 0; i < F.size(); i++) {
          if (std::next(F.begin(), i)->getName() != "for.body895.i.i")
            continue;
          Threads.async([ModulePath = FilePath, FuncName = F.getName().str(), i,
                         &StatLock, &StatCond, &NumProcessedBlocks] {
            runGeneratorOnBasicBlock(ModulePath, FuncName, i);
            {
              std::unique_lock<std::mutex> LockGuard(StatLock);
              NumProcessedBlocks++;
            }
            StatCond.notify_all();
          });
          NumBlocks++;
        }
      }
    }
  }

  errs() << '\n';

  for (;;) {
    unsigned Count = NumProcessedBlocks.load();
    errs() << "\r" << Count << "/" << NumBlocks;
    if (Count == NumBlocks)
      break;
    {
      std::unique_lock<std::mutex> LockGuard(StatLock);
      StatCond.wait(LockGuard,
                    [&] { return NumProcessedBlocks.load() != Count; });
    }
  }

  Threads.wait();
  errs() << '\n';
  return 0;
}
