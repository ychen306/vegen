#include "IntrinsicBuilder.h"
#include "llvm/Support/FormatVariadic.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

using namespace llvm;

Value *IntrinsicBuilder::Create(StringRef Name, ArrayRef<Value *> Operands,
                                unsigned char Imm8) {
  std::string WrapperName =
      formatv("intrinsic_wrapper_{0}_{1}", Name, Imm8).str();
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
    assert(CastInst::castIsValid(Instruction::CastOps::BitCast, Operands[i],
                                 Arg->getType()) &&
           "Invalid input type");
    Value *Operand = CreateBitCast(Operands[i], Arg->getType());
    VMap[Arg] = Operand;
  }

  Value *RetVal = nullptr;
  for (auto &I : BB) {
    if (auto *Ret = dyn_cast<ReturnInst>(&I)) {
      RetVal = Ret->getReturnValue();
      break;
    }
    auto *NewI = I.clone();
    Insert(NewI);
    VMap[&I] = NewI;
    RemapInstruction(NewI, VMap,
                     RF_NoModuleLevelChanges | RF_IgnoreMissingLocals);
    if (auto *CI = dyn_cast<CallInst>(NewI)) {
      auto *Callee = CI->getCalledFunction();
      assert(Callee->isIntrinsic());
      // If the intrinsic wrapper calls an llvm intrinsic,
      // that intrinsic is declared inside `IntrinsicWrappers`.
      // We need to redeclare that intrinsic.
      Module *M = CI->getParent()->getModule();
      FunctionCallee IntrinsicDecl =
          M->getOrInsertFunction(Callee->getName(), Callee->getFunctionType(),
                                 Callee->getAttributes());
      CI->setCalledFunction(cast<Function>(IntrinsicDecl.getCallee()));
    }
  }
  assert(RetVal && "Wrapper not returning explicitly");
  Value *Output = VMap.lookup(RetVal);
  assert(Output);

  return Output;
}
