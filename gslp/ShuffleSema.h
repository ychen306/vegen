#ifndef SHUFFLE_SEMA_H
#define SHUFFLE_SEMA_H

#include "InstSema.h"
#include "llvm/ADT/ArrayRef.h"
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
  unsigned ElementWidth;
  unsigned TotalWidth;
  std::vector<std::vector<InputSlice>> Lanes;

public:
  AbstractSwizzleOutput(unsigned ElementWidth, unsigned TotalWidth,
                        std::vector<std::vector<InputSlice>> Lanes)
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

// interface describing a shuffling/swizzling operation
class Swizzle {
public:
  // Use this to represent imm8 or index vector
  using Parameter = std::vector<uint8_t>;
  // A set of parameter, mapping <input id> -> <parameter>
  using ParameterSet = std::map<unsigned, Parameter>;

  virtual InstSignature getSignature() const = 0;

  virtual AbstractSwizzleOutput getAbstractOutput(unsigned OutputId) const = 0;

  // Try to solve the parameter required to implement this task,
  // return if it's sucessful
  bool solveForParameter(const SwizzleTask &Task,
                         ParameterSet &Parameters) const;

  // emit code that implements a task
  virtual std::vector<VectorPack>
  emit(const SwizzleTask &Task, ParameterSet &Parameters) const = 0;
  // Get the precise semantics of this swizzle kernel
  virtual llvm::ArrayRef<SwizzleOp *> getSemantics() const = 0;
};

#endif
