#ifndef SHUFFLE_SEMA_H
#define SHUFFLE_SEMA_H

#include "InstSema.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/Casting.h"
#include <vector>

class VectorPack {
  unsigned ElementWidth; /* unit = bits */
  std::vector<llvm::Value *> Content;

public:
  VectorPack(unsigned ElementWidth, std::vector<llvm::Value *> Content)
      : ElementWidth(ElementWidth), Content(Content) {}
};

struct SwizzleTask {
  std::vector<VectorPack> Inputs, Outputs;
};

// Interfaces to help indexing this Swizzle, doesn't have to be precise.
class AbstractSwizzleOutput {
public:
  using SliceSet = std::vector<InputSlice>;

private:
  unsigned ElementWidth;
  unsigned TotalWidth;
  std::vector<SliceSet> Lanes;

public:
  AbstractSwizzleOutput(unsigned ElementWidth, unsigned TotalWidth,
                        std::vector<SliceSet> Lanes)
      : ElementWidth(ElementWidth), TotalWidth(TotalWidth), Lanes(Lanes) {
    assert(TotalWidth % ElementWidth == 0);
    // verify that all input lanes have the same element size
    for (auto &PossibleOutputs : Lanes)
      for (auto &Output : PossibleOutputs) {
        assert(Output.size() == ElementWidth);
      }
  }
  llvm::ArrayRef<InputSlice> getLaneOutput(unsigned LaneId) const {
    return Lanes[LaneId];
  }
  unsigned getElementWidth() const { return ElementWidth; }
  unsigned getTotalWidth() const { return TotalWidth; }
  unsigned getNumElements() const { return TotalWidth / ElementWidth; }
};

///////////////////////// BEGIN SHUFFLE OPS ///////////////
// Building blocks for defining a swizzling operation
//  | DymamicSlice (base, idx, stride)
//  | Mux (ctrl : slice) (mapping number -> Slice)
//  | Slice
class SwizzleOp {
public:
  enum OpKind { OK_DynamicSlice, OK_Mux, OK_Slice };

private:
  const OpKind Kind;

public:
  SwizzleOp(OpKind Kind) : Kind(Kind) {}
  OpKind getKind() const { return Kind; }
};

class DynamicSlice : public SwizzleOp {
  SwizzleOp *Base;
  unsigned Stride;
  InputSlice Index;

public:
  DynamicSlice(SwizzleOp *Base, unsigned Stride, InputSlice Index)
      : SwizzleOp(OK_DynamicSlice), Base(Base), Stride(Stride), Index(Index) {}
  SwizzleOp *getBase() const { return Base; }
  unsigned getStride() const { return Stride; }
  const InputSlice &getIndex() const { return Index; }
};

class Mux : public SwizzleOp {
  std::vector<SwizzleOp *> Choices;
  InputSlice Control;

public:
  Mux(std::vector<SwizzleOp *> Choices, InputSlice Control)
      : SwizzleOp(OK_Mux), Choices(Choices), Control(Control) {}
  llvm::ArrayRef<SwizzleOp *> getChoices() const { return Choices; }
};

class Slice : public SwizzleOp {
  InputSlice S;

public:
  Slice(InputSlice S) : SwizzleOp(OK_Slice), S(S) {}
  const InputSlice &getSlice() const { return S; }
};
///////////////////// END SHUFFLE OPS ///////////////////

// Utility interface for emitting swizzle instructions.
class SwizzleValue;
// Use this to represent imm8 or index vector
using Parameter = std::vector<uint8_t>;
// A set of parameter, mapping <input to swizzle inst> -> <parameter>
using ParameterMap = std::map<SwizzleValue *, Parameter>;

struct SwizzleValue {
  using SwizzleEnv = llvm::DenseMap<const SwizzleValue *, llvm::Value *>;
  virtual llvm::Value *emit(SwizzleEnv &Env, IntrinsicBuilder &) const {
    auto It = Env.find(this);
    assert(It != Env.end());
    return It->second;
  }
  virtual SwizzleValue *getParameter() const { return nullptr; }
  virtual llvm::ArrayRef<SwizzleValue *> getOperands() const {
    return llvm::None;
  }
};

class SwizzleInst : public SwizzleValue {
  std::string Name;
  std::vector<SwizzleValue *> Operands;
  // Indicate which of the operand is a parameter (should be statically
  // specified)
  int ParamId;
  bool ParamIsImm;

public:
  SwizzleInst(std::string Name, std::vector<SwizzleValue *> Operands,
              int ParamId = -1, bool ParamIsImm = false)
      : Name(Name), Operands(Operands), ParamId(ParamId),
        ParamIsImm(ParamIsImm) {}
  llvm::Value *emit(SwizzleEnv &Env, IntrinsicBuilder &Builder) const override;
  SwizzleValue *getParameter() const override {
    assert(ParamId >= 0);
    return Operands[ParamId];
  }
  llvm::ArrayRef<SwizzleValue *> getOperands() const override {
    return Operands;
  }
};

// Interface describing a (parametrized) shuffling/swizzling operation
class Swizzle {
public:
  // lanes of swizzle op
  using VectorSemantics = std::vector<SwizzleOp *>;

private:
  InstSignature Sig;
  // The semantics tells us how to solve for the swizzle parameters
  std::vector<VectorSemantics> Semantics;
  std::vector<const SwizzleValue *> Inputs;
  std::vector<const SwizzleValue *> Outputs;
  // Imprecise semantics of this swizzle; used for indexing
  std::vector<AbstractSwizzleOutput> AbstractOutputs;
  // Set of parameters we need to solve in order to implement a concrete swizzle task
  llvm::DenseSet<const SwizzleValue *> ParameterSet;

public:
  Swizzle(InstSignature Sig, std::vector<VectorSemantics> Semantics,
          std::vector<const SwizzleValue *> Inputs,
          std::vector<const SwizzleValue *> Outputs,
          std::vector<AbstractSwizzleOutput> AbstractOutputs);

  AbstractSwizzleOutput getAbstractOutput(unsigned OutputId) const {
    return AbstractOutputs[OutputId];
  }

  const InstSignature &getSignature() { return Sig; }

  // Get the precise semantics of this swizzle kernel,
  // which can have multiple live outs
  llvm::ArrayRef<VectorSemantics> getSemantics() const { return Semantics; }

  // Try to solve the parameter required to implement this task,
  // return if it's sucessful
  bool solveForParameter(const SwizzleTask &Task,
                         ParameterMap &Parameters) const;

  // Emit code to implement a task
  bool emit(const SwizzleTask &Task, const ParameterMap &Parameters) const;
};

#endif
