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
#include <set>

using namespace llvm;
using namespace PatternMatch;

cl::opt<std::string> InstWrappersPath(
    "inst-wrappers",
    cl::desc("Path to InstWrappers.bc"),
    cl::Required);

namespace {

LLVMContext GlobalContext;

std::unique_ptr<Module> InstWrappers;
class GSLP : public ModulePass {
public:
  static char ID; // Pass identification, replacement for typeid
  GSLP() : ModulePass(ID) {
  }

  bool runOnFunction(Function &);

  bool runOnModule(Module &M) override {
    SMDiagnostic Err;
    errs() << "LOADING WRAPPERS\n";
    InstWrappers =
      parseIRFile(InstWrappersPath, Err, M.getContext());
    assert(InstWrappers && "Failed to parse Inst Wrappers");
    errs() << "WRAPPERS LOADED\n";

    bool Changed;
    std::set<Function *> DeleteLater;
    for (Function &F : M) {
      Changed |= runOnFunction(F);
    }

    return Changed;
  }

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
  //auto M = Builder.GetInsertBlock()->getModule();
  //auto *F = M->getFunction(WrapperName);
  auto *F = InstWrappers->getFunction(WrapperName);
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
#define TEST_INST_BINDING 1
#if TEST_INST_BINDING
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
  auto *I = IB->create(IRB, Args);
  OldInst->replaceAllUsesWith(IRB.CreateBitCast(I, OldInst->getType()));
  errs() << F << '\n';
#endif

  assert(!verifyFunction(F));
  return true;
}

// Automatically enable the pass.
// http://adriansampson.net/blog/clangpass.html
static void registerGSLP(const PassManagerBuilder &,
                         legacy::PassManagerBase &PM) {
  PM.add(new GSLP());
}
static RegisterStandardPasses
    RegisterMyPass(PassManagerBuilder::EP_VectorizerStart, registerGSLP);
