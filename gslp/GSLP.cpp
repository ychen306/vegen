#include "InstSema.h"
#include "llvm/Linker/Linker.h"
#include "llvm/IR/Function.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Support/FormatVariadic.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/Analysis/DependenceAnalysis.h"
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
    AU.addRequiredTransitive<DependenceAnalysisWrapperPass>();
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

// Utility class to track dependency within a basic block
class LocalDependenceAnalysis {
  DependenceInfo &DI;
  BasicBlock *BB;
  // mapping inst -> <users>
  DenseMap<Instruction *, std::vector<Instruction *>> Dependencies;

public:
  LocalDependenceAnalysis(DependenceInfo &DI, BasicBlock *BB) : DI(DI), BB(BB) {
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
        // check dependence with preceding loads and stores
        for (auto *PrevLS : LoadStores) {
          auto Dep = DI.depends(PrevLS, &I, true);
          if (Dep && Dep->isOrdered()) {
            Dependencies[&I].push_back(PrevLS);
          }
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

// Emit an intrinsic
template <typename T, typename Inserter>
Value *InstBinding::create(
    Module &InstWrappers,
    IRBuilder<T, Inserter> &Builder,
    ArrayRef<Value *> Operands, unsigned char Imm8) const {
  std::string WrapperName = formatv("intrinsic_wrapper_{0}_{1}", Name, Imm8).str();
  auto *F = InstWrappers.getFunction(WrapperName);
  assert(F && "Intrinsic wrapper undefined.");

  assert(std::distance(F->begin(), F->end()) == 1 &&
      "Intrinsic Wrapper should have a single basic block");
  auto &BB = *F->begin();

  unsigned NumArgs = std::distance(F->arg_begin(), F->arg_end());
  assert(Operands.size() == NumArgs);

  // map wrapper arg to operands
  ValueToValueMapTy VMap;
  for (unsigned i = 0; i < NumArgs; i++) {
    Value *Arg = F->getArg(i);
    assert(
        CastInst::castIsValid(
          Instruction::CastOps::BitCast, Operands[i], Arg->getType()) &&
        "Invalid input type");
    Value *Operand = Builder.CreateBitCast(Operands[i], Arg->getType());
    VMap[Arg] = Operand;
  }

  Value *RetVal = nullptr;
  for (auto &I : BB) {
    if (auto *Ret = dyn_cast<ReturnInst>(&I)) {
      RetVal = Ret->getReturnValue();
      break;
    }
    auto *NewI = I.clone();
    Builder.Insert(NewI);
    VMap[&I] = NewI;
    RemapInstruction(NewI, VMap, 
        RF_NoModuleLevelChanges | RF_IgnoreMissingLocals);
  }
  assert(RetVal && "Wrapper not returning explicitly");
  Value *Output = VMap.lookup(RetVal);
  assert(Output);

  return Output;
}

char GSLP::ID = 0;

bool GSLP::runOnFunction(Function &F) {
#if 1
  DependenceInfo &DI = getAnalysis<DependenceAnalysisWrapperPass>().getDI();
  for (auto &BB : F) {
    LocalDependenceAnalysis LDA(DI, &BB);
    for (auto &I : BB) {
      for (auto &PrevI : BB) {
        if (&I == &PrevI)
          break;
        errs() << "CHECKING DEPENDENCE: " << PrevI << " -> " << I << '\n';
        errs() << "\t" << LDA.hasLocalDependence(&PrevI, &I) << '\n';
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
INITIALIZE_PASS_DEPENDENCY(DependenceAnalysisWrapperPass)
INITIALIZE_PASS_END(GSLP, "gslp", "gslp", false, false)

// Automatically enable the pass.
// http://adriansampson.net/blog/clangpass.html
static void registerGSLP(const PassManagerBuilder &,
                         legacy::PassManagerBase &PM) {
  PM.add(new GSLP());
}
static RegisterStandardPasses
    RegisterMyPass(PassManagerBuilder::EP_VectorizerStart, registerGSLP);
