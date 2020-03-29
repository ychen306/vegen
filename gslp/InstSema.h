#ifndef INST_SEMA_H
#define INST_SEMA_H

#include "llvm/ADT/APInt.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/FormatVariadic.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include <vector>

namespace llvm {
class TargetTransformInfo;
}

struct InstSignature {
  std::vector<unsigned> InputBitwidths;
  std::vector<unsigned> OutputBitwidths;
  bool HasImm8;
  unsigned numInputs() const { return InputBitwidths.size(); }
  unsigned numOutputs() const { return OutputBitwidths.size(); }
};

struct InputSlice {
  unsigned InputId;
  unsigned Lo, Hi;

  unsigned size() { return Hi - Lo; }

  bool operator<(const InputSlice &Other) const {
    return std::tie(InputId, Lo, Hi) <
           std::tie(Other.InputId, Other.Lo, Other.Hi);
  }
};

// Interface that abstractly defines an operation
struct Operation {
  struct Match {
    std::vector<llvm::Value *> Inputs;
    // FIXME: make this an Instruction instead
    llvm::Value *Output;
    bool operator<(const Match &Other) const {
      return std::tie(Output, Inputs) < std::tie(Other.Output, Other.Inputs);
    }
    bool operator==(const Match &Other) const {
      return Output == Other.Output && Inputs == Other.Inputs;
    }
  };
  // `match' returns true if `V` is matched.
  // If a match is found, additionally return the matched liveins
  virtual bool match(llvm::Value *V, std::vector<Match> &Matches) const = 0;
};

// An operation explicitly bound to an instruction and its input(s)
class BoundOperation {
  const Operation *Op;
  std::vector<InputSlice> BoundSlices;

public:
  // A bound operation
  BoundOperation(const Operation *Op, std::vector<InputSlice> BoundSlices)
      : Op(Op), BoundSlices(BoundSlices) {}
  const Operation *getOperation() const { return Op; }
  llvm::ArrayRef<InputSlice> getBoundSlices() const { return BoundSlices; }
};

class IntrinsicBuilder : public llvm::IRBuilder<> {
  llvm::Module &InstWrappers;

public:
  llvm::LLVMContext &getContext() { return InstWrappers.getContext(); }
  using InsertPoint = llvm::IRBuilderBase::InsertPoint;
  IntrinsicBuilder(llvm::Module &InstWrappers)
      : llvm::IRBuilder<>(InstWrappers.getContext()),
        InstWrappers(InstWrappers) {}

  llvm::Value *Create(llvm::StringRef Name,
                      llvm::ArrayRef<llvm::Value *> Operands,
                      unsigned char Imm8 = 0) {
    using namespace llvm;

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
};

// An instruction is a list of lanes,
// each of which characterized by a BoundOperation
class InstBinding {
  InstSignature Sig;
  std::string Name;
  std::vector<std::string> TargetFeatures;
  std::vector<BoundOperation> LaneOps;

public:
  virtual int getCost(llvm::TargetTransformInfo *, llvm::LLVMContext &) const {
    return 1;
  }
  llvm::ArrayRef<std::string> getTargetFeatures() const {
    return TargetFeatures;
  }
  InstBinding(std::string Name, std::vector<std::string> TargetFeatures,
              InstSignature Sig, std::vector<BoundOperation> LaneOps)
      : Name(Name), TargetFeatures(TargetFeatures), Sig(Sig), LaneOps(LaneOps) {
  }
  const InstSignature &getSignature() const { return Sig; }
  llvm::ArrayRef<BoundOperation> getLaneOps() const { return LaneOps; }
  virtual llvm::Value *emit(llvm::ArrayRef<llvm::Value *> Operands,
                            IntrinsicBuilder &Builder) const {
    return Builder.Create(Name, Operands);
  }
  llvm::StringRef getName() const { return Name; }
};

static bool hasBitWidth(const llvm::Value *V, unsigned BitWidth) {
  auto *Ty = V->getType();
  if (Ty->isIntegerTy())
    return Ty->getIntegerBitWidth() == BitWidth;
  if (Ty->isFloatTy())
    return BitWidth == 32;
  if (Ty->isDoubleTy())
    return BitWidth == 64;
  return false;
}

extern std::vector<InstBinding> Insts;

#endif // end INST_SEMA_H
