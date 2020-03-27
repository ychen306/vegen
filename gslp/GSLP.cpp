#include "InstSema.h"
#include "LocalDependenceAnalysis.h"
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

namespace llvm {
void initializeGSLPPass(PassRegistry &);
}

namespace {

bool isFloat(Instruction::BinaryOps Opcode) {
  switch (Opcode) {
  case Instruction::FAdd:
  case Instruction::FSub:
  case Instruction::FMul:
  case Instruction::FDiv:
  case Instruction::FRem:
    return true;
  default:
    return false;
  }
}

class BinaryIROperation : public Operation {
  const Instruction::BinaryOps Opcode;
  unsigned Bitwidth;

public:
  BinaryIROperation(Instruction::BinaryOps Opcode, unsigned Bitwidth)
      : Opcode(Opcode), Bitwidth(Bitwidth) {}
  std::string getName() const { return Instruction::getOpcodeName(Opcode); }
  unsigned getBitwidth() const { return Bitwidth; }
  const Instruction::BinaryOps getOpcode() const { return Opcode; }
  bool match(llvm::Value *V, std::vector<Match> &Matches) const override {
    auto *BinOp = dyn_cast<BinaryOperator>(V);
    bool Matched =
        BinOp && BinOp->getOpcode() == Opcode && hasBitWidth(BinOp, Bitwidth);
    if (Matched)
      Matches.push_back({// live ins of this operation
                         {BinOp->getOperand(0), BinOp->getOperand(1)},
                         V});
    return Matched;
  }
};

class IRVectorBinding : public InstBinding {
  const BinaryIROperation *Op;

  IRVectorBinding(const BinaryIROperation *Op, std::string Name,
                  InstSignature Sig, std::vector<BoundOperation> LaneOps)
      : InstBinding(Name, {} /* no target features required*/, Sig, LaneOps),
        Op(Op) {}

public:
  static IRVectorBinding Create(const BinaryIROperation *Op,
                                unsigned VectorWidth);
  virtual Value *emit(ArrayRef<llvm::Value *> Operands,
                      IntrinsicBuilder &Builder) const override;
  int getCost(TargetTransformInfo *TTI, LLVMContext &Ctx) const override {
    Type *ScalarTy;
    unsigned ElemWidth = Op->getBitwidth();
    auto Opcode = Op->getOpcode();
    if (isFloat(Opcode)) {
      assert(ElemWidth == 32 || ElemWidth == 64);
      if (ElemWidth == 32)
        ScalarTy = Type::getFloatTy(Ctx);
      else
        ScalarTy = Type::getDoubleTy(Ctx);
    } else {
      ScalarTy = IntegerType::get(Ctx, ElemWidth);
    }
    unsigned NumElems = getLaneOps().size();
    auto *VecTy = VectorType::get(ScalarTy, NumElems);
    return TTI->getArithmeticInstrCost(Opcode, VecTy);
  }
};

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

  bool runOnFunction(Function &) override;

  virtual bool doInitialization(Module &M) override {
    SMDiagnostic Err;
    errs() << "LOADING WRAPPERS\n";
    InstWrappers = parseIRFile(InstWrappersPath, Err, M.getContext());
    assert(InstWrappers && "Failed to parse Inst Wrappers");
    errs() << "WRAPPERS LOADED\n";

    return false;
  }
};

std::vector<Instruction::BinaryOps> VectorizableOpcodes = {
    Instruction::BinaryOps::Add,  Instruction::BinaryOps::FAdd,
    Instruction::BinaryOps::Sub,  Instruction::BinaryOps::FSub,
    Instruction::BinaryOps::Mul,  Instruction::BinaryOps::FMul,
    Instruction::BinaryOps::UDiv, Instruction::BinaryOps::SDiv,
    Instruction::BinaryOps::FDiv, Instruction::BinaryOps::URem,
    Instruction::BinaryOps::SRem, Instruction::BinaryOps::FRem,
    Instruction::BinaryOps::Shl,  Instruction::BinaryOps::LShr,
    Instruction::BinaryOps::AShr, Instruction::BinaryOps::And,
    Instruction::BinaryOps::Or,   Instruction::BinaryOps::Xor};

// Aux class enumerating vector ir that we can emit
class VectorizableTable {
  std::vector<BinaryIROperation> VectorizableOps;
  std::vector<IRVectorBinding> VectorInsts;

  std::vector<InstBinding *> Bindings;

public:
  VectorizableTable() {
    // enumerate vectorizable scalar ops
    std::vector<unsigned> ScalarBitwidths = {8, 16, 32, 64};
    for (auto Opcode : VectorizableOpcodes)
      for (unsigned SB : ScalarBitwidths) {
        if (isFloat(Opcode) && SB != 32 && SB != 64)
          continue;
        VectorizableOps.emplace_back(Opcode, SB);
      }

    // enumerate vector insts
    std::vector<unsigned> VectorBitwidths = {64, 128, 256};
    for (auto &Op : VectorizableOps) {
      for (unsigned VB : VectorBitwidths) {
        // Skip singleton pack
        if (VB / Op.getBitwidth() == 1)
          continue;
        VectorInsts.emplace_back(IRVectorBinding::Create(&Op, VB));
      }
    }

    for (auto &Binding : VectorInsts)
      Bindings.push_back(&Binding);
  }

  ArrayRef<InstBinding *> getBindings() const { return Bindings; }

} VecBindingTable;

// This class pulls all operation that we are interested in
// and tries to match all of them while trying to avoid
// matching the same operation twice on the same value
class MatchManager {
  // record matches for each operation
  DenseMap<const Operation *, std::vector<Operation::Match>> Matches;

public:
  MatchManager(ArrayRef<InstBinding *> Insts) {
    for (auto &Inst : Insts)
      for (auto &LaneOp : Inst->getLaneOps())
        Matches.FindAndConstruct(LaneOp.getOperation());
  }

  void match(Value *V) {
    for (auto &KV : Matches) {
      const Operation *Op = KV.first;
      std::vector<Operation::Match> &Matches = KV.second;
      Op->match(V, Matches);
    }
  }

  llvm::ArrayRef<Operation::Match> getMatches(const Operation *Op) const {
    auto It = Matches.find(Op);
    assert(It != Matches.end());
    return It->second;
  }
};

struct MCMCVectorPackSet : public VectorPackSet {
  MCMCVectorPackSet(Function *F) : VectorPackSet(F) {}
  std::unique_ptr<VectorPack> removeRandomPack();
};

// Mapping a load/store -> a set of consecutive loads/stores
//
// This is basically a generalization of a store/load chain.
// We use a DAG because a load, for example, might have multiple
// "next" candidate.
using ConsecutiveAccessDAG =
    DenseMap<Instruction *, SmallPtrSet<Instruction *, 4>>;

bool isScalarType(Type *Ty) { return Ty->getScalarType() == Ty; }

bool hasFeature(const Function &F, std::string Feature) {
  Attribute Features = F.getFnAttribute("target-features");
  return !Features.hasAttribute(Attribute::None) &&
         Features.getValueAsString().contains("+" + Feature);
}

bool isSupported(InstBinding *Inst, const Function &F) {
  for (auto &Feature : Inst->getTargetFeatures())
    if (!hasFeature(F, Feature))
      return false;
  return true;
}

} // end anonymous namespace

// Do a quadratic search to build the access dags
template <typename MemAccessTy>
void buildAccessDAG(ConsecutiveAccessDAG &DAG, ArrayRef<MemAccessTy *> Accesses,
                    const DataLayout *DL, ScalarEvolution *SE) {
  for (auto *A1 : Accesses) {
    // Get type of the value being acccessed
    auto *Ty =
        cast<PointerType>(A1->getPointerOperand()->getType())->getElementType();
    if (!isScalarType(Ty))
      continue;
    for (auto *A2 : Accesses) {
      if (A1->getType() == A2->getType() &&
          isConsecutiveAccess(A1, A2, *DL, *SE))
        DAG[A1].insert(A2);
    }
  }
};

IRVectorBinding IRVectorBinding::Create(const BinaryIROperation *Op,
                                        unsigned VectorWidth) {
  // Compute the signature of this BINARY vector inst
  InstSignature Sig = {// bitwidths of the inputs
                       {VectorWidth, VectorWidth},
                       // bitwidth of the output
                       {VectorWidth},
                       // has imm8?
                       false};

  unsigned ElemWidth = Op->getBitwidth();
  assert(VectorWidth % ElemWidth == 0);
  unsigned NumLanes = VectorWidth / ElemWidth;
  std::vector<BoundOperation> LaneOps;
  for (int i = 0; i < NumLanes; i++) {
    unsigned Lo = i * ElemWidth, Hi = Lo + ElemWidth;
    LaneOps.push_back(BoundOperation(Op,
                                     // input binding
                                     {{0, Lo, Hi}, {1, Lo, Hi}}));
  }

  return IRVectorBinding(Op, Op->getName(), Sig, LaneOps);
}

Value *IRVectorBinding::emit(llvm::ArrayRef<llvm::Value *> Operands,
                             IntrinsicBuilder &Builder) const {
  assert(Operands.size() == 2);
  Instruction::BinaryOps Opcode = Op->getOpcode();
  return Builder.CreateBinOp(Opcode, Operands[0], Operands[1]);
}

char GSLP::ID = 0;

// Sample an integer between 0 and N.
static unsigned rand_int(int N) { return std::rand() % N; }

// Sample a float between 0 and 1
float rand_float() {
  float r = (float)rand() / (float)RAND_MAX;
  return r;
}

// sample indenpdent, consecutive memory accesses
template <typename MemAccessTy>
static std::tuple<std::vector<MemAccessTy *>, BitVector, BitVector>
sampleAccesses(const ConsecutiveAccessDAG &DAG, VectorPackContext &VPCtx,
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

  return {Accesses, Elements, Depended};
}

static Optional<VectorPack> sampleLoadPack(ConsecutiveAccessDAG &LoadDAG,
                                           VectorPackContext &VPCtx,
                                           LocalDependenceAnalysis &LDA,
                                           unsigned MaxNumLoads,
                                           unsigned NumTrials = 8) {
  std::vector<LoadInst *> Loads;
  BitVector Elements;
  BitVector Depended;
  while (NumTrials--) {
    std::tie(Loads, Elements, Depended) =
        sampleAccesses<LoadInst>(LoadDAG, VPCtx, LDA, MaxNumLoads);
    if (Loads.size() > 1)
      break;
  }
  if (Loads.size() <= 1)
    return None;
  return VPCtx.createLoadPack(Loads, Elements, Depended);
}

static Optional<VectorPack> sampleStorePack(ConsecutiveAccessDAG &StoreDAG,
                                            VectorPackContext &VPCtx,
                                            LocalDependenceAnalysis &LDA,
                                            unsigned MaxNumStores,
                                            unsigned NumTrials = 16) {
  std::vector<StoreInst *> Stores;
  BitVector Elements;
  BitVector Depended;
  while (NumTrials--) {
    std::tie(Stores, Elements, Depended) =
        sampleAccesses<StoreInst>(StoreDAG, VPCtx, LDA, MaxNumStores);
    if (Stores.size() > 1)
      break;
  }
  if (Stores.size() <= 1)
    return None;
  return VPCtx.createStorePack(Stores, Elements, Depended);
}

static VectorPack
samplePhiPack(DenseMap<Type *, SmallVector<PHINode *, 4>> &PHIs,
              VectorPackContext &VPCtx, unsigned MaxNumPHIs) {
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
  return VPCtx.createPhiPack(SelectedPHIs);
}

// TODO: support NOOP lanes
//
static Optional<VectorPack> sampleVectorPack(const MatchManager &MM,
                                             VectorPackContext &VPCtx,
                                             LocalDependenceAnalysis &LDA,
                                             const InstBinding *Inst,
                                             unsigned NumTrials) {

  while (NumTrials--) {
    BitVector Elements(VPCtx.getNumValues());
    BitVector Depended(VPCtx.getNumValues());

    // Fill each lane...
    bool Success = true;
    std::vector<llvm::Optional<Operation::Match>> Matches;
    for (auto &LaneOp : Inst->getLaneOps()) {
      // FIXME: need to distinguish between an arithmetic operation and
      // "pass-through" We allow a value to pass through multiple operation. But
      // we only allow a value to be *produced* at a single pack.
      //
      // Figure out available independent packs
      std::vector<const Operation::Match *> IndependentMatches;
      for (auto &M : MM.getMatches(LaneOp.getOperation())) {
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
      Matches.push_back(*SelectedM);
      assert(Elements.count() == Matches.size());
    }

    if (Success) {
      auto VP = VPCtx.createVectorPack(Matches, Elements, Depended, Inst);
      return VP;
    }
  }

  return None;
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

std::unique_ptr<VectorPack> MCMCVectorPackSet::removeRandomPack() {
  auto It = std::next(AllPacks.begin(), rand_int(AllPacks.size()));
  auto *VP = It->get();
  auto *BB = VP->getBasicBlock();

  // Find the local iterator
  auto &LocalPacks = Packs[BB];
  auto LocalIt = std::find(LocalPacks.begin(), LocalPacks.end(), VP);
  assert(LocalIt != LocalPacks.end());

  // Delete the pack pointer from the basic block index
  eraseUnordered(LocalPacks, LocalIt);
  // Delete the pack itself
  std::unique_ptr<VectorPack> Removed(It->release());
  eraseUnordered(AllPacks, It);

  removeAux(Removed.get());

  NumPacks--;
  return Removed;
}

template <typename InstTy>
Optional<std::vector<InstTy *>>
castOperandPack(const VectorPack::OperandPack &OpndPack) {
  std::vector<InstTy *> Ret;
  for (auto *V : OpndPack) {
    auto *I = dyn_cast<InstTy>(V);
    if (!I)
      return None;
    Ret.push_back(I);
  }
  return Ret;
}

// Find vector packs that produces operand pack
static void extendWithDef(const VectorPack::OperandPack &OpndPack,
                          std::vector<VectorPack> &Extensions,
                          ConsecutiveAccessDAG &LoadDAG, const MatchManager &MM,
                          const VectorPackContext &VPCtx,
                          LocalDependenceAnalysis &LDA,
                          const SmallPtrSet<const InstBinding *, 4> &Insts) {
  auto *BB = VPCtx.getBasicBlock();

  BitVector Elements(VPCtx.getNumValues());
  BitVector Depended(VPCtx.getNumValues());

  // First, check if the operand pack is indepdendent.
  // We can't extend if it's not independent.
  for (Value *V : OpndPack) {
    // Also bail if we can't produce this pack at current basic block
    auto *I = dyn_cast<Instruction>(V);
    if (!I)
      return;
    if (I->getParent() != BB)
      return;

    // Check dependence
    unsigned ValueId = VPCtx.getScalarId(I);
    if (Elements.test(ValueId))
      return;

    BitVector Depended2 = LDA.getDepended(I);
    if (Depended.test(ValueId))
      return;
    if (Depended2.anyCommon(Elements))
      return;

    Elements.set(ValueId);
    Depended |= Depended2;
  }

  if (auto LoadsOrNull = castOperandPack<LoadInst>(OpndPack)) {
    std::vector<LoadInst *> Loads;
    SmallPtrSet<LoadInst *, 4> LoadSet(LoadsOrNull->begin(),
                                       LoadsOrNull->end());
    for (auto *LI : LoadsOrNull.getValue()) {
      SmallPtrSet<LoadInst *, 4> LoadsRemained = LoadSet;
      // See if there's a proper ordering of these loads starting from `LI`,
      // so that they are consecutive.
      LoadsRemained.erase(LI);
      LoadInst *CurLoad = LI;
      Loads = {LI};
      while (!LoadsRemained.empty()) {
        auto It = LoadDAG.find(CurLoad);
        if (It == LoadDAG.end())
          break;
        LoadInst *NextLoad = nullptr;
        for (auto *I : It->second) {
          auto *LI = cast<LoadInst>(I);
          if (LoadsRemained.erase(LI)) {
            NextLoad = LI;
            break;
          }
        }
        if (!NextLoad)
          break;
        Loads.push_back(NextLoad);
        CurLoad = NextLoad;
      }
      if (Loads.size() == LoadSet.size())
        break;
    }
    if (Loads.size() != LoadSet.size())
      return;
    Extensions.push_back(VPCtx.createLoadPack(Loads, Elements, Depended));
    return;
  }

  if (auto PHIsOrNull = castOperandPack<PHINode>(OpndPack)) {
    Extensions.push_back(VPCtx.createPhiPack(PHIsOrNull.getValue()));
    return;
  }

  // NOTE: We can't extend with Store packs vector stores don't produce
  // anything...

  // Aux func to enumerate cross product of `LaneMatches`
  auto EnumeratePacks =
      [&](const InstBinding *Inst,
          const std::vector<std::vector<Operation::Match>> &LaneMatches) {
        unsigned NumLanes = Inst->getLaneOps().size();
        assert(NumLanes == LaneMatches.size());
        unsigned N = 1;
        for (auto &Matches : LaneMatches)
          N *= Matches.size();
        for (unsigned i = 0; i < N; i++) {
          // `i` represent a particular member of the cross product.
          // Decode `i` here.
          std::vector<Optional<Operation::Match>> Lanes;
          for (auto &Matches : LaneMatches) {
            unsigned M = Matches.size();
            assert(M);
            Lanes.push_back(Matches[i % M]);
            i /= M;
          }

          Extensions.push_back(
              VPCtx.createVectorPack(Lanes, Elements, Depended, Inst));
        }
      };

  for (auto *Inst : Insts) {
    // See if we can pack with this Inst
    ArrayRef<BoundOperation> LaneOps = Inst->getLaneOps();
    unsigned NumLanes = LaneOps.size();
    if (NumLanes != OpndPack.size())
      continue;
    std::vector<std::vector<Operation::Match>> LaneMatches(NumLanes);
    bool Feasible = true;
    unsigned LaneId = 0;
    for (const auto &LaneOp : LaneOps) {
      ArrayRef<Operation::Match> Matches = MM.getMatches(LaneOp.getOperation());
      if (Matches.empty()) {
        Feasible = false;
        break;
      }
      for (auto &Match : Matches) {
        if (Match.Output == OpndPack[LaneId]) {
          LaneMatches[LaneId].push_back(Match);
        }
      }
      LaneId++;
    }
    if (!Feasible)
      continue;
    EnumeratePacks(Inst, LaneMatches);
  }
}

bool GSLP::runOnFunction(Function &F) {
  //if (F.getName() != "binvcrhs")
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
    auto MM = std::make_unique<MatchManager>(SupportedInsts);
    for (auto &I : BB) {
      MM->match(&I);
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
      Optional<VectorPack> VPOrNull =
          sampleVectorPack(*MMs[&BB], *VPCtxs[&BB], *LDAs[&BB], Inst, 1000);
      if (VPOrNull)
        InstBindings[&BB].insert(Inst);
    }
  }

  unsigned ProbLoad = 20;
  unsigned ProbStore = 60;
  unsigned ProbPhi = 5;
  unsigned ProbGeneral = 15;

  auto ExtendOnePack = [&]() -> bool {
    if (Packs.getNumPacks() == 0)
      return false;
    // Sample a random pack to extend
    auto &VP = Packs.getPack(rand_int(Packs.getNumPacks()));
    std::vector<VectorPack> Extensions;
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

      extendWithDef(OpndPack, Extensions, *LoadDAGs[BB], *MMs[BB], *VPCtxs[BB],
                    *LDAs[BB], InstBindings[BB]);
    }
    if (Extensions.empty())
      return false;
    return Packs.tryAdd(Extensions[rand_int(Extensions.size())]);
  };

  unsigned NumInsts = F.getInstructionCount();

  auto SampleOnePack = [&]() -> bool {
    auto &RandInst =
        *std::next(inst_begin(F), rand_int(NumInsts));
    auto *BB = RandInst.getParent();

    if (LoadDAGs[BB]->empty())
      ProbLoad = 0;
    if (StoreDAGs[BB]->empty())
      ProbStore = 0;
    unsigned PTotal = ProbLoad + ProbStore + ProbPhi + ProbGeneral;
    if (!PTotal)
      return false;
    unsigned P = rand_int(PTotal);

    if (P < ProbLoad) {
      auto &LoadDAG = *LoadDAGs[BB];
      if (LoadDAG.empty())
        return false;
      auto LoadPackOrNull = sampleLoadPack(LoadDAG, *VPCtxs[BB], *LDAs[BB], 16);
      return LoadPackOrNull && Packs.tryAdd(LoadPackOrNull.getValue());
    }
    P -= ProbLoad;

    if (P < ProbStore) {
      auto &StoreDAG = *StoreDAGs[BB];
      if (StoreDAG.empty())
        return false;
      auto StorePackOrNull =
          sampleStorePack(StoreDAG, *VPCtxs[BB], *LDAs[BB], 16);
      return StorePackOrNull && Packs.tryAdd(StorePackOrNull.getValue());
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
      if (PHIs.empty()) {
        ProbPhi = 0;
        return false;
      }
      return Packs.tryAdd(samplePhiPack(PHIs, *VPCtxs[BB], 4));
    }

    const auto &Bindings = InstBindings[BB];
    if (Bindings.empty())
      return false;
    // FIXME: refactor all of these `std::next(... rand_int))` stuff
    auto *Inst = *std::next(Bindings.begin(), rand_int(Bindings.size()));
    Optional<VectorPack> VPOrNull =
        sampleVectorPack(*MMs[BB], *VPCtxs[BB], *LDAs[BB], Inst, 32);
    return VPOrNull && Packs.tryAdd(VPOrNull.getValue());
  };

#if 0
  auto BestPacks = Packs;
  float BestCost = 0;
  for (int i = 0; i < 1000; i++) {
    Packs = MCMCVectorPackSet(&F);
    // bool Sampled = SampleOnePack();
    SampleOnePack();
    for (int j = 0; j < 100; j++)
      ExtendOnePack();
    float Cost = Packs.getCostSaving(TTI, BFI);
    // if (Sampled || Cost < BestCost) {
    //  for (int i = 0; i < Packs.getNumPacks(); i++)
    //    errs() << Packs.getPack(i) << '\n';
    //  errs() << F << '\n';
    //  BestCost = Cost;
    //  BestPacks = Packs;
    //  break;
    //}
    // break;
    if (Cost < BestCost) {
      errs() << "COST: " << Cost << ", NUM PACKS: " << Packs.getNumPacks() << '\n';
      BestCost = Cost;
      BestPacks = Packs;
    }
  }
#else
  const unsigned NumIters = 1000000;
  const float Beta = 0.4;

  float BestCost = 0.0;
  VectorPackSet BestPacks(&F);
  float Cost = 0.0;
  for (int i = 0; i < NumIters; i++) {
    if (i % 1000 == 0)
      errs() << "COST: " << Cost << ", NUM PACKS: " << Packs.getNumPacks()
             << ", ITER: " << i << '\n';
    std::unique_ptr<VectorPack> Removed;
    if (Packs.getNumPacks() && rand_int(100) < 51) {
      Removed = Packs.removeRandomPack();
    } else {
      bool Changed = false;
      if (Packs.getNumPacks() && rand_int(10) < 8)
        Changed = ExtendOnePack();
      if (!Changed)
        Changed = SampleOnePack();
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
