#include "InstSema.h"
#include "ShuffleSema.h"
#include "llvm/Linker/Linker.h"
#include "llvm/IR/Function.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/MemoryLocation.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/InitializePasses.h"
#include <set>

using namespace llvm;
using namespace PatternMatch;

cl::opt<std::string> InstWrappersPath(
    "inst-wrappers",
    cl::desc("Path to InstWrappers.bc"),
    cl::Required);

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
  }

  bool runOnFunction(Function &) override;

  virtual bool doInitialization(Module &M) override {
    SMDiagnostic Err;
    errs() << "LOADING WRAPPERS\n";
    InstWrappers =
      parseIRFile(InstWrappersPath, Err, M.getContext());
    assert(InstWrappers && "Failed to parse Inst Wrappers");
    errs() << "WRAPPERS LOADED\n";

    return false;
  }

};

MemoryLocation getLocation(Instruction *I, AliasAnalysis *AA) {              
  if (StoreInst *SI = dyn_cast<StoreInst>(I))                                       
    return MemoryLocation::get(SI);                                                 
  if (LoadInst *LI = dyn_cast<LoadInst>(I))                                         
    return MemoryLocation::get(LI);                                                 
  return MemoryLocation();                                                          
}

/// \returns True if the instruction is not a volatile or atomic load/store.
bool isSimple(Instruction *I) {
  if (LoadInst *LI = dyn_cast<LoadInst>(I))
    return LI->isSimple();
  if (StoreInst *SI = dyn_cast<StoreInst>(I))
    return SI->isSimple();
  if (MemIntrinsic *MI = dyn_cast<MemIntrinsic>(I))
    return !MI->isVolatile();
  return true;
}

bool isAliased(const MemoryLocation &Loc1,
    Instruction *Inst1, Instruction *Inst2, AliasAnalysis *AA) {
  MemoryLocation Loc2 = getLocation(Inst2, AA);
  bool Aliased = true;
  if (Loc1.Ptr && Loc2.Ptr && isSimple(Inst1) && isSimple(Inst2)) {
    // Do the alias check.
    Aliased = AA->alias(Loc1, Loc2);
  }
  return Aliased;
}

// Utility class to track dependency within a basic block
class LocalDependenceAnalysis {
  BasicBlock *BB;
  // mapping inst -> <users>
  DenseMap<Instruction *, std::vector<Instruction *>> Dependencies;

  public:
  LocalDependenceAnalysis(AliasAnalysis *AA, BasicBlock *BB) : BB(BB) {
    std::vector<Instruction *> LoadStores;
    // build the local dependence graph
    for (Instruction &I : *BB) {
      for (Value *Operand : I.operands()) {
        if (auto *I2 = dyn_cast<Instruction>(Operand))
          if (I2->getParent() == BB) {
            Dependencies[&I].push_back(I2);
          }
      }
      if (isa<LoadInst>(&I) || isa<StoreInst>(&I)) {
        MemoryLocation Loc = getLocation(&I, AA);
        // check dependence with preceding loads and stores
        for (auto *PrevLS : LoadStores) {
          // ignore output dependence
          if (isa<LoadInst>(PrevLS) && isa<LoadInst>(&I))
            continue;
          if (isAliased(Loc, &I, PrevLS, AA))
            Dependencies[&I].push_back(PrevLS);
        }
        LoadStores.push_back(&I);
      }
    }
  }

  bool hasLocalDependence(Instruction *Src, Instruction *Dest) {
    if (Src->getParent() != BB || Dest->getParent() != BB)
      return false;

    // Check if `Src` is reachable from `Dest` in the local dependency graph
    std::vector<Instruction *> Worklist { Dest };
    DenseSet<Instruction *> Visited;
    while (!Worklist.empty()) {
      Instruction *I = Worklist.back();
      Worklist.pop_back();

      if (I == Src)
        return true;

      bool Inserted = Visited.insert(I).second;
      if (!Inserted)
        continue;

      // this is a DAG, so we don't have to worry about seeing a node twice
      auto &Depended = Dependencies[I];
      Worklist.insert(Worklist.end(), Depended.begin(), Depended.end());
    }
    return false;
  }
};

} // end anonymous namespace


char GSLP::ID = 0;

bool GSLP::runOnFunction(Function &F) {
#if 1
  AliasAnalysis *AA = &getAnalysis<AAResultsWrapperPass>().getAAResults();
  for (auto &BB : F) {
    LocalDependenceAnalysis LDA(AA, &BB);
    for (auto &I : BB) {
      for (auto &PrevI : BB) {
        if (&I == &PrevI)
          break;
        //errs() << "CHECKING DEPENDENCE: " << PrevI << " -> " << I << '\n';
        //errs() << "\t" << LDA.hasLocalDependence(&PrevI, &I) << '\n';
      }
    }
  }
#endif
#if 0
  InstBinding *IB;
  for (auto &I : Insts) {
    if (I.getName() == "_mm_add_ss") {
      IB = &I;
      break;
    }
  }
  auto &BB = *F.begin();
  auto *OldInst = &*BB.begin();
  IRBuilder<> IRB(&BB, BB.begin());
  std::vector<Value *> Args;
  for (auto &Arg : F.args()) {
    Args.push_back(&Arg);
  }
  auto *I = IB->create(*InstWrappers, IRB, Args);
  OldInst->replaceAllUsesWith(IRB.CreateBitCast(I, OldInst->getType()));
  errs() << F << '\n';
#endif

  assert(!verifyFunction(F));
  return true;
}

INITIALIZE_PASS_BEGIN(GSLP, "gslp", "gslp", false, false)
INITIALIZE_PASS_DEPENDENCY(ScalarEvolutionWrapperPass)
INITIALIZE_PASS_DEPENDENCY(AAResultsWrapperPass)
INITIALIZE_PASS_END(GSLP, "gslp", "gslp", false, false)

// Automatically enable the pass.
// http://adriansampson.net/blog/clangpass.html
static void registerGSLP(const PassManagerBuilder &,
    legacy::PassManagerBase &PM) {
  PM.add(new GSLP());
}
static RegisterStandardPasses
RegisterMyPass(PassManagerBuilder::EP_VectorizerStart, registerGSLP);
