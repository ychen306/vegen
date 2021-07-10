#include "IRVec.h"
#include "InstSema.h"
#include "Packer.h"
#include "Solver.h"
#include "Unroll.h"
#include "VectorPackSet.h"
#include "llvm/ADT/Triple.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopIterator.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/InitializePasses.h"
#include "llvm/Linker/Linker.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/Cloning.h"      // CloneBasicBlock
#include "llvm/Transforms/Utils/LoopSimplify.h" // simplifyLoop
#include "llvm/Transforms/Utils/LoopUtils.h"    // cloneLoop
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
    WrappersDir("wrappers-dir",
                cl::desc("Path to the directory containing InstWrappers.*.bc"),
                cl::Required);

static cl::opt<std::string>
    Filter("filter",
           cl::desc("only run on function names containing this substring"));

static cl::opt<bool> UseMainlineSLP("use-slp", cl::desc("Use LLVM SLP"),
                                    cl::init(false));

namespace llvm {
void initializeGSLPPass(PassRegistry &);
}

namespace {

class GSLP : public FunctionPass {
  std::unique_ptr<Module> InstWrappers;
  Triple::ArchType Arch;

  std::vector<InstBinding> &getInsts() const {
    switch (Arch) {
    case Triple::x86_64:
      return X86Insts;
    case Triple::aarch64:
      return ArmInsts;
    default:
      llvm_unreachable("unsupported target architecture");
    }
  }

public:
  static char ID; // Pass identification, replacement for typeid
  GSLP() : FunctionPass(ID) {
    initializeGSLPPass(*PassRegistry::getPassRegistry());
  }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<LoopInfoWrapperPass>();
    AU.addRequired<DominatorTreeWrapperPass>();
    AU.addRequired<AssumptionCacheTracker>();
    AU.addRequired<ScalarEvolutionWrapperPass>();
    AU.addRequired<AAResultsWrapperPass>();
    AU.addRequired<TargetTransformInfoWrapperPass>();
    AU.addRequired<BlockFrequencyInfoWrapperPass>();
  }

  bool runOnFunction(llvm::Function &) override;

  virtual bool doInitialization(Module &M) override {
    Arch = Triple(M.getTargetTriple()).getArch();
    SMDiagnostic Err;
    std::string Wrapper;
    switch (Arch) {
    case Triple::x86_64:
      Wrapper = "/x86.bc";
      break;
    case Triple::aarch64:
      Wrapper = "/arm.bc";
      break;

    default:
      llvm_unreachable("architecture not supported");
    }
    errs() << "Loading inst wrappers: " << WrappersDir + Wrapper << '\n';
    InstWrappers = parseIRFile(WrappersDir + Wrapper, Err, M.getContext());
    if (!InstWrappers) {
      report_fatal_error(std::string("Error parsing Inst Wrappers") +
                         Err.getMessage());
    }

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

void vectorizeBasicBlock(BasicBlock &BB, VectorPackSet &Packs, Packer &Pkr) {
  VectorPackSet PacksScratch = Packs;
  float BottomUpCost = optimizeBottomUp(PacksScratch, &Pkr, &BB);
  errs() << "Bottom-up cost: " << BottomUpCost << '\n';
  Packs = PacksScratch;
  return;
}

} // namespace

char GSLP::ID = 0;

static SmallVector<Value *, 4>
collectReductionElements(Instruction *I,
                         std::vector<Instruction *> &Intermediates) {
  SmallVector<Value *, 4> Elems;

  std::vector<Value *> Worklist{I};
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
  auto *A = buildBalancedTree(IRB, Leaves.drop_back(N / 2 /*num drop*/));
  auto *B = buildBalancedTree(
      IRB, Leaves.slice(N - N / 2 /*num drop*/, N / 2 /*num keep*/));
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

        // errs() << "MATCHED AND BALANCED REDUCTION : (\n";
        // for (auto *V : Elems)
        //  errs() << *V << '\n';
        // errs() << ")\n";
      }
    }
  }
}

static Loop *cloneLoop(Loop *L, LoopInfo *LI, DominatorTree *DT) {
  ValueToValueMapTy VMap;
  std::vector<BasicBlock *> NewBlocks;
  auto Clone = [&](BasicBlock *BB) -> BasicBlock * {
    BasicBlock *NewBB = CloneBasicBlock(BB, VMap, "", BB->getParent());
    VMap[BB] = NewBB;
    NewBlocks.push_back(NewBB);
    return NewBB;
  };
  auto *Preheader = L->getLoopPreheader();
  DT->addNewBlock(Clone(Preheader),
                  DT->getNode(Preheader)->getIDom()->getBlock());
  for (auto *BB : L->getBlocks())
    DT->addNewBlock(Clone(BB), Preheader);
  for (auto *BB : L->getBlocks()) {
    BasicBlock *Dominator = DT->getNode(BB)->getIDom()->getBlock();
    DT->changeImmediateDominator(cast<BasicBlock>(VMap[BB]),
                                 cast<BasicBlock>(VMap[Dominator]));
  }
  Loop *NewL = cloneLoop(L, nullptr /*parent loop*/, VMap, LI,
                         nullptr /*lppassmanager*/);
  for (auto *BB : NewBlocks)
    for (auto &I : *BB)
      RemapInstruction(&I, VMap,
                       RF_NoModuleLevelChanges | RF_IgnoreMissingLocals);
  for (auto *BB : NewBlocks)
    errs() << "!!! cloned: " << *BB << '\n';
  return NewL;
}

static void removeInstsFromBlock(BasicBlock *BB) {
  std::vector<Instruction *> Instructions;
  for (auto &I : *BB) {
    I.replaceAllUsesWith(UndefValue::get(I.getType()));
    Instructions.push_back(&I);
  }
  for (auto *I : Instructions)
    I->eraseFromParent();
}

bool GSLP::runOnFunction(Function &F) {
  if (!Filter.empty() && !F.getName().contains(Filter))
    return false;
  // balanceReductionTree(F);
  // Table holding all IR vector instructions
  IRInstTable VecBindingTable;

  auto *AA = &getAnalysis<AAResultsWrapperPass>().getAAResults();
  auto *SE = &getAnalysis<ScalarEvolutionWrapperPass>().getSE();
  auto *TTI = &getAnalysis<TargetTransformInfoWrapperPass>().getTTI(F);
  auto *BFI = &getAnalysis<BlockFrequencyInfoWrapperPass>().getBFI();
  auto *DL = &F.getParent()->getDataLayout();

  // Stuff to deal with loops
  auto *LI = &getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
  auto *DT = &getAnalysis<DominatorTreeWrapperPass>().getDomTree();
  auto *AC = &getAnalysis<AssumptionCacheTracker>().getAssumptionCache(F);

  {
    for (auto &BB : F) {
      if (Loop *L = LI->getLoopFor(&BB)) {
        formLCSSARecursively(*L, *DT, LI, SE);
        simplifyLoop(L, DT, LI, SE, AC, nullptr, true);
        if (!L->isLCSSAForm(*DT)) {
          errs() << "???????????? bug: not in lcssa form\n";
          abort();
        }
        if (!L->getLoopPreheader()) {
          errs() << "???????????? bug: no preheader\n";
          abort();
        }
        Loop *NewL = cloneLoop(L, LI, DT);

        UnrollLoopOptions ULO;
        ULO.TripCount = 0;
        ULO.Count = 2;
        ULO.Force = true;
        ULO.PeelCount = 0;
        ULO.AllowRuntime = true;
        ULO.AllowExpensiveTripCount = true;
        ULO.ForgetAllSCEV = false;
        ULO.UnrollRemainder = true;

        for (auto *BB : L->blocks())
          for (auto &I : *BB)
            if (SE->isSCEVable(I.getType()))
              errs() << "scev: " << I << ", " << *SE->getSCEV(&I) << '\n';

        ValueMap<const Value *, UnrolledValue> OrigToUnrollMap;
        auto Result =
            UnrollLoopWithVMap(NewL, ULO, LI, SE, nullptr /*DT*/, AC, TTI, true,
                               OrigToUnrollMap, nullptr /*remainder loop*/);
        errs() << "??? unroll result: "
               << (Result != LoopUnrollResult::Unmodified) << '\n';

        errs() << "??? unrolled loop: <<<<<<\n";
        for (auto *BB : NewL->blocks())
          errs() << *BB << '\n';
        errs() << ">>>>>>>>>>\n";

        BasicBlock *PH = NewL->getLoopPreheader();
        for (auto *BB : NewL->blocks())
          removeInstsFromBlock(BB);
        removeInstsFromBlock(PH);
        for (auto *BB : NewL->blocks())
          BB->eraseFromParent();
        PH->eraseFromParent();
        LI->removeLoop(std::find(LI->begin(), LI->end(), NewL));
        LI->destroy(NewL);
      }
    }
  }
  errs() << F << '\n';
  return false;

  std::vector<const InstBinding *> SupportedIntrinsics;
  for (InstBinding &Inst : getInsts())
    if (isSupported(&Inst, F))
      SupportedIntrinsics.push_back(&Inst);
  for (auto &Inst : VecBindingTable.getBindings()) {
    if (Inst.isSupported(TTI))
      SupportedIntrinsics.push_back(&Inst);
  }

  errs() << "~~~~ num supported intrinsics: " << SupportedIntrinsics.size()
         << '\n';
  Packer Pkr(SupportedIntrinsics, F, AA, DL, SE, TTI, BFI);
  VectorPackSet Packs(&F);
  for (auto &BB : F) {
    errs() << "Optimizing " << F.getName() << "/" << BB.getName() << '\n';
    vectorizeBasicBlock(BB, Packs, Pkr);
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
INITIALIZE_PASS_DEPENDENCY(AssumptionCacheTracker)
INITIALIZE_PASS_DEPENDENCY(DominatorTreeWrapperPass)
INITIALIZE_PASS_DEPENDENCY(LoopInfoWrapperPass)
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
