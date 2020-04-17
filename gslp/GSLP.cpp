#include "IRModel.h" // NOTE: this file has to be included first because of namespace conflict with libtorch
#include "IRVec.h"
#include "InstSema.h"
#include "LocalDependenceAnalysis.h"
#include "MatchManager.h"
#include "Packer.h"
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
#include "llvm/Analysis/OrderedBasicBlock.h"
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

struct MCMCVectorPackSet : public VectorPackSet {
  MCMCVectorPackSet(llvm::Function *F) : VectorPackSet(F) {}
  const VectorPack *removeRandomPack();
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

} // end anonymous namespace

char GSLP::ID = 0;

// Sample a float between 0 and 1
float rand_float() {
  float r = (float)rand() / (float)RAND_MAX;
  return r;
}

// sample indenpdent, consecutive memory accesses
template <typename MemAccessTy>
static std::tuple<std::vector<MemAccessTy *>, BitVector, BitVector>
sampleAccesses(const VectorPackSet &ExistingPacks,
               const ConsecutiveAccessDAG &DAG, VectorPackContext &VPCtx,
               LocalDependenceAnalysis &LDA, unsigned MaxNumAccesses) {
  // Pick a seed to start the chain
  auto DAGIt = std::next(DAG.begin(), rand_int(DAG.size()));
  auto *LastAccess = cast<MemAccessTy>(DAGIt->first);
  auto *NextAccesses = &DAGIt->second;
  BitVector Elements(VPCtx.getNumValues());
  Elements.set(VPCtx.getScalarId(LastAccess));
  BitVector Depended = LDA.getDepended(LastAccess);

  std::vector<MemAccessTy *> Accesses{LastAccess};
  assert(Elements.count() == Accesses.size());
  while (Accesses.size() < MaxNumAccesses) {

    // Find independent candidate to extend this chain of loads
    SmallVector<MemAccessTy *, 4> IndependentAccesses;
    for (auto *A : *NextAccesses) {
      if (ExistingPacks.isPacked(A, VPCtx))
        continue;
      auto Depended2 = LDA.getDepended(A);
      unsigned AccessId = VPCtx.getScalarId(A);
      if (Elements.anyCommon(Depended2) || Depended.test(AccessId))
        continue;
      IndependentAccesses.push_back(cast<MemAccessTy>(A));
    }

    // Abort if we don't have anything to choose from
    if (IndependentAccesses.empty())
      break;

    // Sample one of the candidates
    LastAccess = IndependentAccesses[rand_int(IndependentAccesses.size())];
    Accesses.push_back(LastAccess);
    Depended |= LDA.getDepended(LastAccess);
    Elements.set(VPCtx.getScalarId(LastAccess));

    auto It = DAG.find(LastAccess);
    // This load doesn't have any consecutive load that follows
    if (It == DAG.end())
      break;
    NextAccesses = &It->second;
    assert(Elements.count() == Accesses.size());
  }

  return std::tuple<std::vector<MemAccessTy *>, BitVector, BitVector>(Accesses, Elements, Depended);
}

static VectorPack *
sampleLoadPack(const VectorPackSet &ExistingPacks,
               ConsecutiveAccessDAG &LoadDAG, VectorPackContext &VPCtx,
               LocalDependenceAnalysis &LDA, TargetTransformInfo *TTI,
               unsigned MaxNumLoads, unsigned NumTrials = 128) {
  std::vector<LoadInst *> Loads;
  BitVector Elements;
  BitVector Depended;
  while (NumTrials--) {
    std::tie(Loads, Elements, Depended) = sampleAccesses<LoadInst>(
        ExistingPacks, LoadDAG, VPCtx, LDA, MaxNumLoads);
    if (Loads.size() > 1)
      break;
  }
  if (Loads.size() <= 1)
    return nullptr;
  return VPCtx.createLoadPack(Loads, Elements, Depended, TTI);
}

static VectorPack *
sampleStorePack(const VectorPackSet &ExistingPacks,
                ConsecutiveAccessDAG &StoreDAG, VectorPackContext &VPCtx,
                LocalDependenceAnalysis &LDA, TargetTransformInfo *TTI,
                unsigned MaxNumStores, unsigned NumTrials = 128) {
  std::vector<StoreInst *> Stores;
  BitVector Elements;
  BitVector Depended;
  while (NumTrials--) {
    std::tie(Stores, Elements, Depended) = sampleAccesses<StoreInst>(
        ExistingPacks, StoreDAG, VPCtx, LDA, MaxNumStores);
    if (Stores.size() > 1)
      break;
  }
  if (Stores.size() <= 1)
    return nullptr;
  return VPCtx.createStorePack(Stores, Elements, Depended, TTI);
}

static VectorPack *
samplePhiPack(DenseMap<Type *, SmallVector<PHINode *, 4>> &PHIs,
              VectorPackContext &VPCtx, TargetTransformInfo *TTI,
              unsigned MaxNumPHIs) {
  // NOTE: All phi nodes within a basic block are always locally independent
  // so we don't need to query the dependence analysis.

  // Now choose one group of isomorphic phis.
  auto It = std::next(PHIs.begin(), rand_int(PHIs.size()));
  auto &IsoPHIs = It->second;
  // Shuffle these phis before we pack them
  std::random_shuffle(IsoPHIs.begin(), IsoPHIs.end(), rand_int);
  unsigned NumPHIs = std::min<unsigned>(IsoPHIs.size(), MaxNumPHIs);
  std::vector<PHINode *> SelectedPHIs(IsoPHIs.begin(),
                                      std::next(IsoPHIs.begin(), NumPHIs));
  return VPCtx.createPhiPack(SelectedPHIs, TTI);
}

// TODO: support NOOP lanes
//
static VectorPack *
sampleVectorPack(const VectorPackSet &ExistingPacks, const MatchManager &MM,
                 VectorPackContext &VPCtx, LocalDependenceAnalysis &LDA,
                 const InstBinding *Inst, TargetTransformInfo *TTI,
                 unsigned NumTrials) {

  while (NumTrials--) {
    BitVector Elements(VPCtx.getNumValues());
    BitVector Depended(VPCtx.getNumValues());

    // Fill each lane...
    bool Success = true;
    std::vector<const Operation::Match *> Matches;
    for (auto &LaneOp : Inst->getLaneOps()) {
      // FIXME: need to distinguish between an arithmetic operation and
      // "pass-through" We allow a value to pass through multiple operation. But
      // we only allow a value to be *produced* at a single pack.
      //
      // Figure out available independent packs
      std::vector<const Operation::Match *> IndependentMatches;
      for (auto &M : MM.getMatches(LaneOp.getOperation())) {
        if (auto *I = dyn_cast<Instruction>(M.Output))
          if (ExistingPacks.isPacked(I, VPCtx))
            continue;
        unsigned OutputId = VPCtx.getScalarId(M.Output);
        // This value has already been packed
        if (Elements.test(OutputId))
          continue;
        auto Depended2 = LDA.getDepended(cast<Instruction>(M.Output));
        // Selcted values depends on this one
        if (Depended.test(OutputId))
          continue;
        // This one depends on selected values
        if (Depended2.anyCommon(Elements))
          continue;
        IndependentMatches.push_back(&M);
      }
      if (IndependentMatches.empty()) {
        Success = false;
        break;
      }

      // Choose one of the independent mathes
      auto *SelectedM = IndependentMatches[rand_int(IndependentMatches.size())];
      Elements.set(VPCtx.getScalarId(SelectedM->Output));
      Depended |= LDA.getDepended(cast<Instruction>(SelectedM->Output));
      Matches.push_back(SelectedM);
      assert(Elements.count() == Matches.size());
    }

    if (Success)
      return VPCtx.createVectorPack(Matches, Elements, Depended, Inst, TTI);
  }

  return nullptr;
}

// Erase stuff from a vector when we don't care about ordering within the vector
template <typename T>
void eraseUnordered(std::vector<T> &Container,
                    typename std::vector<T>::iterator It) {
  // first swap the stuff we want to delete to the end
  auto LastIt = std::prev(Container.end());
  std::iter_swap(It, LastIt);
  Container.pop_back();
}

const VectorPack *MCMCVectorPackSet::removeRandomPack() {
  auto It = std::next(AllPacks.begin(), rand_int(AllPacks.size()));
  auto *VP = *It;
  auto *BB = VP->getBasicBlock();

  // Find the local iterator
  auto &LocalPacks = Packs[BB];
  auto LocalIt = std::find(LocalPacks.begin(), LocalPacks.end(), VP);
  assert(LocalIt != LocalPacks.end());

  // Delete the pack pointer from the basic block index
  eraseUnordered(LocalPacks, LocalIt);
  // Delete the pack itself
  eraseUnordered(AllPacks, It);

  removeAux(VP);

  NumPacks--;
  return VP;
}

bool GSLP::runOnFunction(llvm::Function &F) {
  // if (F.getName() != "adi")
  //  return false;
  // if (F.getName() != "binvcrhs")
  // return false;
  // if (F.getName() != "cmul_many")
  //  return false;
  auto *AA = &getAnalysis<AAResultsWrapperPass>().getAAResults();
  auto *SE = &getAnalysis<ScalarEvolutionWrapperPass>().getSE();
  auto *TTI = &getAnalysis<TargetTransformInfoWrapperPass>().getTTI(F);
  auto *BFI = &getAnalysis<BlockFrequencyInfoWrapperPass>().getBFI();

  auto *DL = &F.getParent()->getDataLayout();

  // Figure out vector instructions we can use
  std::vector<InstBinding *> SupportedInsts;
#define USE_INTRINSICS 0

#ifndef USE_INTRINSICS
#define USE_INTRINSICS 0
#endif

#if USE_INTRINSICS
  errs() << "Using vector intrinsics.\n";
  std::vector<InstBinding *> AvailableInsts;
  for (auto &Inst : Insts)
    AvailableInsts.push_back(&Inst);
#else
  errs() << "Using LLVM IR vectors.\n";
  std::vector<InstBinding *> AvailableInsts = VecBindingTable.getBindings();
#endif
  for (auto *Inst : AvailableInsts) {
    if (isSupported(Inst, F))
      SupportedInsts.push_back(Inst);
  }
  errs() << "Num supported insts: " << SupportedInsts.size() << '\n';

  // FIXME: fuse all of these together into a single map
  DenseMap<BasicBlock *, std::unique_ptr<MatchManager>> MMs;
  DenseMap<BasicBlock *, std::unique_ptr<LocalDependenceAnalysis>> LDAs;
  DenseMap<BasicBlock *, std::unique_ptr<ConsecutiveAccessDAG>> LoadDAGs;
  DenseMap<BasicBlock *, std::unique_ptr<ConsecutiveAccessDAG>> StoreDAGs;
  DenseMap<BasicBlock *, std::unique_ptr<VectorPackContext>> VPCtxs;

  // Setup analyses and determine search space
  for (auto &BB : F) {
    std::vector<LoadInst *> Loads;
    std::vector<StoreInst *> Stores;
    // Find packable instructions
    auto MM = std::make_unique<MatchManager>(SupportedInsts, BB);
    for (auto &I : BB) {
      if (auto *LI = dyn_cast<LoadInst>(&I)) {
        if (LI->isSimple())
          Loads.push_back(LI);
      } else if (auto *SI = dyn_cast<StoreInst>(&I)) {
        if (SI->isSimple())
          Stores.push_back(SI);
      }
    }

    auto VPCtx = std::make_unique<VectorPackContext>(&BB);
    auto LoadDAG = std::make_unique<ConsecutiveAccessDAG>();
    auto StoreDAG = std::make_unique<ConsecutiveAccessDAG>();
    buildAccessDAG<LoadInst>(*LoadDAG, Loads, DL, SE);
    buildAccessDAG<StoreInst>(*StoreDAG, Stores, DL, SE);

    MMs[&BB] = std::move(MM);
    LDAs[&BB] = std::make_unique<LocalDependenceAnalysis>(AA, &BB, VPCtx.get());
    VPCtxs[&BB] = std::move(VPCtx);
    LoadDAGs[&BB] = std::move(LoadDAG);
    StoreDAGs[&BB] = std::move(StoreDAG);
  }

  MCMCVectorPackSet Packs(&F);
  std::srand(42);

  // First find out if which vector instruction we can emit.
  // E.g. sometimes there is simply no `fadd` in a basic block..
  DenseMap<BasicBlock *, SmallPtrSet<const InstBinding *, 4>> InstBindings;
  for (auto *Inst : SupportedInsts) {
    for (auto &BB : F) {
      auto VPOrNull = sampleVectorPack(Packs, *MMs[&BB], *VPCtxs[&BB],
                                       *LDAs[&BB], Inst, TTI, 1000);
      if (VPOrNull)
        InstBindings[&BB].insert(Inst);
    }
  }

  unsigned ProbLoad = 20;
  unsigned ProbStore = 60;
  unsigned ProbPhi = 5;
  unsigned ProbGeneral = 15;

  auto FindExtensionForOnePack = [&](const VectorPack &VP,
                                     const VectorPackSet &Packs,
                                     std::vector<VectorPack *> &Extensions) {
    for (auto &OpndPack : VP.getOperandPacks()) {
      // Figure out where the scalar operands are produced.
      // Bail if they are produced in different basic blocks.
      BasicBlock *BB = nullptr;
      bool FromSingleBB = true;
      for (auto *V : OpndPack) {
        auto *I = dyn_cast<Instruction>(V);
        if (!I)
          continue;
        if (!BB)
          BB = I->getParent();
        else if (I->getParent() != BB) {
          FromSingleBB = false;
          break;
        }
      }
      // Can't extend from this operand pack
      if (!FromSingleBB || !BB)
        break;

      extendWithDef(OpndPack, Packs, Extensions, LoadDAGs, MMs, VPCtxs, LDAs,
                    InstBindings, TTI);
    }
  };

  auto ExtendOnePack = [&](VectorPackSet &Packs) -> bool {
    if (Packs.getNumPacks() == 0)
      return false;
    // Sample a random pack to extend
    auto &VP = Packs.getPack(rand_int(Packs.getNumPacks()));
    std::vector<VectorPack *> Extensions;
    FindExtensionForOnePack(VP, Packs, Extensions);
    if (Extensions.empty())
      return false;
    return Packs.tryAdd(Extensions[rand_int(Extensions.size())]);
  };

  unsigned NumInsts = F.getInstructionCount();

  // FIXME: shouldn't reset the Prob* parameters
  auto SampleOnePackFromBB = [&](VectorPackSet &Packs,
                                 BasicBlock *BB) -> const VectorPack * {
    unsigned PTotal = ProbLoad + ProbStore + ProbPhi + ProbGeneral;
    if (!PTotal)
      return nullptr;
    unsigned P = rand_int(PTotal);

    if (P < ProbLoad) {
      auto &LoadDAG = *LoadDAGs[BB];
      if (LoadDAG.empty())
        return nullptr;
      return sampleLoadPack(Packs, LoadDAG, *VPCtxs[BB], *LDAs[BB], TTI, 16);
    }
    P -= ProbLoad;

    if (P < ProbStore) {
      auto &StoreDAG = *StoreDAGs[BB];
      if (StoreDAG.empty())
        return nullptr;
      return sampleStorePack(Packs, StoreDAG, *VPCtxs[BB], *LDAs[BB], TTI, 8);
    }
    P -= ProbStore;

    if (P < ProbPhi) {
      // FIXME: do this in a preprocessing pass
      DenseMap<Type *, SmallVector<PHINode *, 4>> PHIs;
      // Group the phi nodes by their types
      for (auto &PHI : BB->phis()) {
        if (!isScalarType(PHI.getType()))
          continue;
        PHIs[PHI.getType()].push_back(&PHI);
      }
      if (PHIs.empty())
        return nullptr;
      return samplePhiPack(PHIs, *VPCtxs[BB], TTI, 4);
    }

    const auto &Bindings = InstBindings[BB];
    if (Bindings.empty())
      return nullptr;
    // FIXME: refactor all of these `std::next(... rand_int))` stuff
    auto *Inst = *std::next(Bindings.begin(), rand_int(Bindings.size()));
    return sampleVectorPack(Packs, *MMs[BB], *VPCtxs[BB], *LDAs[BB], Inst, TTI,
                            32);
  };

  auto SampleOnePack = [&](VectorPackSet &Packs) -> bool {
    auto &RandInst = *std::next(inst_begin(F), rand_int(NumInsts));
    auto *BB = RandInst.getParent();
    auto VPOrNull = SampleOnePackFromBB(Packs, BB);
    return VPOrNull && Packs.tryAdd(VPOrNull);
  };

  std::vector<VectorPack *> Extensions;
  VectorPackSet ScratchPacks(&F), BestExtended(&F);
  auto EvalSeedPacks = [&](const VectorPackSet &Packs,
                           unsigned Alpha =
                               4) -> std::pair<VectorPackSet *, float> {
    unsigned NumTrials = Alpha * Packs.getNumPacks();
    float BestCost = Packs.getCostSaving(TTI, BFI);
    BestExtended = Packs;
    for (unsigned i = 0; i < NumTrials; i++) {
      ScratchPacks = Packs;
      bool Changed;
      unsigned FirstUnprocessedPackId = 0;
      do {
        Changed = false;
        Extensions.clear();
        for (unsigned i = FirstUnprocessedPackId;
             i < ScratchPacks.getNumPacks(); i++)
          FindExtensionForOnePack(ScratchPacks.getPack(i), ScratchPacks,
                                  Extensions);
        FirstUnprocessedPackId = ScratchPacks.getNumPacks() - 1;
        random_shuffle(Extensions.begin(), Extensions.end(), rand_int);
        for (auto *VP : Extensions)
          Changed |= ScratchPacks.tryAdd(VP);
      } while (Changed);
      float Cost = ScratchPacks.getCostSaving(TTI, BFI);
      if (Cost < BestCost) {
        BestCost = Cost;
        BestExtended = ScratchPacks;
      }
    }
    return {&BestExtended, BestCost};
  };

  auto EvalSeedPack = [&](const VectorPack &VP) -> float {
    VectorPackSet Packs(&F);
    Packs.tryAdd(&VP);
    return EvalSeedPacks(Packs).second;
  };

  /////////
  const unsigned BatchSize = 4096;

  Packer Packer(SupportedInsts, F, AA, DL, SE, TTI, BFI);

  // FIXME: make sure ths supported insts we are using here syncs up with the model
  PackModel Model(32, SupportedInsts);
  loadModel(Model, ModelPath);

  auto PackDistr = Packer.runModel(torch::Device(torch::kCPU), Model, 8);

#if 1
  // Sample Seed packs and evaluate their qualities
  std::map<const VectorPack *, float> SeedPacks;
  VectorPackSet EmptyPackSet(&F);
  for (auto &I : make_range(inst_begin(F), inst_end(F))) {
    for (int i = 0; i < 8; i++) {
      auto *VP = Packer.samplePackForInst(&I, Packs, PackDistr).VP;
      if (!VP || SeedPacks.count(VP))
        continue;
      SeedPacks[VP] = EvalSeedPack(*VP);
    }
  }

  std::vector<const VectorPack *> ProfitableSeedPacks;
  for (auto &VPAndCost : SeedPacks)
    if (VPAndCost.second < 0)
      ProfitableSeedPacks.push_back(VPAndCost.first);

  std::sort(ProfitableSeedPacks.begin(), ProfitableSeedPacks.end(),
            [&](const VectorPack *A, const VectorPack *B) {
              return SeedPacks[A] < SeedPacks[B];
            });

  if (ProfitableSeedPacks.empty())
    return false;

  const unsigned NumIters = 100000;
  const float Beta = 0.8;

  float BestCost = 0.0;
  float Cost = 0.0;
  std::vector<unsigned> SeedPackIds, BestSeedPackIds;
#if 0
  for (int i = 0; i < NumIters; i++) {
    VectorPackSet Packs(&F);

    int RemovedId = -1, AddedId = -1;

    // remove a random seed
    if (rand_int(2) == 0 && !SeedPackIds.empty()) {
      std::random_shuffle(SeedPackIds.begin(), SeedPackIds.end(), rand_int);
      RemovedId = SeedPackIds.back();
      SeedPackIds.pop_back();
      for (unsigned Id : SeedPackIds)
        Packs.tryAdd(ProfitableSeedPacks[Id]);
    } else {
      for (unsigned Id : SeedPackIds)
        Packs.tryAdd(ProfitableSeedPacks[Id]);
      // add a seed
      unsigned Fuel = 128;
      bool Added = false;
      while (Fuel--) {
        unsigned SeedId = rand_int(ProfitableSeedPacks.size());
        auto &VP = ProfitableSeedPacks[SeedId];
        Added = Packs.tryAdd(VP);
        if (Added) {
          AddedId = SeedId;
          SeedPackIds.push_back(SeedId);
          break;
        }
      }
      if (!Added)
        continue;
    }

    float NewCost = EvalSeedPacks(Packs, 32).second;
    errs() << "COST: " << Cost << ", CAND COST: " << NewCost
           << ", NUM SEEDS: " << SeedPackIds.size() << ", ITER: " << i << '\n';

    if (NewCost < Cost - logf(rand_float()) / Beta) {
      Cost = NewCost;
      if (Cost < BestCost) {
        BestCost = Cost;
        BestSeedPackIds = SeedPackIds;
      }
    } else {
      if (AddedId >= 0)
        SeedPackIds.pop_back();
      else {
        assert(RemovedId >= 0);
        SeedPackIds.push_back(RemovedId);
      }
    }
  }

  MCMCVectorPackSet BestSeedPacks(&F);
  for (unsigned Id : BestSeedPackIds)
    BestSeedPacks.tryAdd(ProfitableSeedPacks[Id]);
  auto BestPacks = EvalSeedPacks(BestSeedPacks, 128).first;
#else

  VectorPackSet BestPacks(&F);
  Cost = 0.0;
  errs() << "NUM PROFITABLE SEEDS: " << ProfitableSeedPacks.size() << '\n';
  for (auto *VP : ProfitableSeedPacks) {
    if (!BestPacks.tryAdd(VP))
      continue;
    float NewCost = EvalSeedPacks(BestPacks, 8).second;
    errs() << "NEW COST: " << NewCost << ", BEST COST: " << Cost
           << ", NUM SEED PACKS: " << BestPacks.getNumPacks() << '\n';
    if (NewCost >= Cost)
      BestPacks.pop();
    else
      Cost = NewCost;
  }
  errs() << "COST: " << Cost << '\n';
  BestPacks = *EvalSeedPacks(BestPacks, 128).first;
#endif

#endif

#if 0
  const unsigned NumIters = 100000;
  const float Beta = 0.5;

  float BestCost = 0.0;
  VectorPackSet BestPacks(&F);
  float Cost = 0.0;
  for (int i = 0; i < NumIters; i++) {
    if (i % 1000 == 0)
      errs() << "COST: " << Cost << ", NUM PACKS: " << Packs.getNumPacks()
             << ", ITER: " << i << '\n';
    std::unique_ptr<VectorPack> Removed;
    if (Packs.getNumPacks() && rand_int(100) < 60) {
      Removed = Packs.removeRandomPack();
    } else {
      bool Changed = false;
      if (Packs.getNumPacks() && rand_int(8) < 7)
        Changed = ExtendOnePack(Packs);
      if (!Changed)
        Changed = SampleOnePack(Packs);
      if (!Changed)
        continue;
    }
    float NewCost = Packs.getCostSaving(TTI, BFI);
    if (NewCost < Cost - logf(rand_float()) / Beta) {
      Cost = NewCost;
      if (Cost < BestCost) {
        BestCost = Cost;
        BestPacks = Packs;
      }
    } else {
      if (Removed)
        Packs.tryAdd(*Removed);
      else
        Packs.pop();
    }
  }
#endif

  IntrinsicBuilder Builder(*InstWrappers);
  BestPacks.codegen(Builder, LDAs);

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
