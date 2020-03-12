#ifndef INST_SEMA_H
#define INST_SEMA_H

#include "llvm/IR/Value.h"
#include "llvm/ADT/APInt.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/IR/IRBuilder.h"
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
    return std::tie(InputId, Lo, Hi)
      < std::tie(Other.InputId, Other.Lo, Other.Hi);
  }
};

// Interface that abstractly defines an operation
struct Operation {
  struct Match {
    std::vector<llvm::Value *> Inputs;
    llvm::Value *Output;
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
  using InsertPoint = llvm::IRBuilderBase::InsertPoint;
  IntrinsicBuilder(InsertPoint IP, llvm::Module &InstWrappers)
  : llvm::IRBuilder<>(InstWrappers.getContext()), InstWrappers(InstWrappers) {
    assert(&IP.getBlock()->getContext() == &InstWrappers.getContext());

    SetInsertPoint(IP.getBlock(), IP.getPoint());
  }

  llvm::Value *Create(
      llvm::StringRef Name,
      llvm::ArrayRef<llvm::Value *> Operands,
      unsigned char Imm8=0) {
    using namespace llvm;
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
  std::vector<BoundOperation> LaneOps;
  std::string Name;
  
public:
  virtual int getCost(llvm::TargetTransformInfo *, llvm::LLVMContext &) const { return -1; }
  InstBinding(std::string Name, InstSignature Sig, std::vector<BoundOperation> LaneOps) 
    : Name(Name), Sig(Sig), LaneOps(LaneOps) {}
  const InstSignature &getSignature() const { return Sig; }
  llvm::ArrayRef<BoundOperation> getLaneOps() const { return LaneOps; }
  virtual llvm::Value *emit(llvm::ArrayRef<llvm::Value *> Operands, IntrinsicBuilder &Builder) const {
    return Builder.Create(Name, Operands);
  }
};

template <typename LHS_TY, typename RHS_TY>
llvm::PatternMatch::CmpClass_match<LHS_TY, RHS_TY, llvm::CmpInst, llvm::CmpInst::Predicate> 
m_Cmp_dont_care(llvm::CmpInst::Predicate Pred, LHS_TY LHS, RHS_TY RHS) {
  return llvm::PatternMatch::m_Cmp(Pred, LHS, RHS);
}

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
