#ifndef INST_SEMA_H
#define INST_SEMA_H

#include "IntrinsicBuilder.h"
#include "llvm/ADT/APInt.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/IR/Value.h"
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
  virtual ~Operation() {}
  struct Match {
    bool Commutative; // applies when the operation is binary
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

// An instruction is a list of lanes,
// each of which characterized by a BoundOperation
class InstBinding {
  InstSignature Sig;
  std::string Name;
  std::vector<std::string> TargetFeatures;
  std::vector<BoundOperation> LaneOps;
  llvm::Optional<float> Cost;

public:
  InstBinding(std::string Name, std::vector<std::string> TargetFeatures,
              InstSignature Sig, std::vector<BoundOperation> LaneOps,
              llvm::Optional<float> Cost = llvm::None)
      : Sig(Sig), Name(Name), TargetFeatures(TargetFeatures), LaneOps(LaneOps),
        Cost(Cost) {}
  virtual ~InstBinding() {}
  virtual float getCost(llvm::TargetTransformInfo *,
                        llvm::LLVMContext &) const {
    assert(Cost.hasValue());
    return Cost.getValue();
  }
  llvm::ArrayRef<std::string> getTargetFeatures() const {
    return TargetFeatures;
  }
  const InstSignature &getSignature() const { return Sig; }
  llvm::ArrayRef<BoundOperation> getLaneOps() const { return LaneOps; }
  virtual llvm::Value *emit(llvm::ArrayRef<llvm::Value *> Operands,
                            IntrinsicBuilder &Builder) const {
    return Builder.Create(Name, Operands);
  }
  llvm::StringRef getName() const { return Name; }
};

static inline bool hasBitWidth(const llvm::Value *V, unsigned BitWidth) {
  auto *Ty = V->getType();
  if (Ty->isIntegerTy())
    return Ty->getIntegerBitWidth() == BitWidth;
  if (Ty->isFloatTy())
    return BitWidth == 32;
  if (Ty->isDoubleTy())
    return BitWidth == 64;
  return false;
}

extern std::vector<InstBinding> X86Insts;
extern std::vector<InstBinding> ArmInsts;

#endif // end INST_SEMA_H
