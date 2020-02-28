#ifndef SHUFFLE_SEMA_H
#define SHUFFLE_SEMA_H

#include "llvm/IR/Value.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/Support/Casting.h"
#include "InstSema.h"
#include <vector>

class VectorPack {
  unsigned ElementWidth; /* unit = bits */
  std::vector<llvm::Value *> Content;
public:
  VectorPack(unsigned ElementWidth, std::vector<llvm::Value *> Content) :
    ElementWidth(ElementWidth), Content(Content) {}
};

struct ShuffleTask {
  std::vector<VectorPack> Inputs, Outputs;
};

// Interfaces to help indexing this Shuffle, doesn't have to be precise.
class AbstractShuffleOutput {
  unsigned ElementWidth;
  unsigned TotalWidth;
  std::vector<std::vector<InputSlice>> Lanes;
public:
  AbstractShuffleOutput(
      unsigned ElementWidth, unsigned TotalWidth,
      std::vector<std::vector<InputSlice>> Lanes) :
    ElementWidth(ElementWidth),
    TotalWidth(TotalWidth),
    Lanes(Lanes) {
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
class ShuffleOp {
public:
  enum OpKind {
    OK_DynamicSlice,
    OK_Mux,
    OK_Slice
  };
private:
  const OpKind Kind;
public:
  ShuffleOp(OpKind Kind) : Kind(Kind) {}
  OpKind getKind() const { return Kind; }
};

class DynamicSlice : public ShuffleOp {
  ShuffleOp *Base;
  unsigned Stride;
  InputSlice Index;
public:
  DynamicSlice(ShuffleOp *Base, unsigned Stride, InputSlice Index) :
    ShuffleOp(OK_DynamicSlice), Base(Base), Stride(Stride), Index(Index) {}
  ShuffleOp *getBase() const { return Base; }
  unsigned getStride() const { return Stride; }
};

class Mux : public ShuffleOp {
  std::vector<ShuffleOp *> Choices;
  InputSlice Control;
public:
  Mux(std::vector<ShuffleOp *> Choices, InputSlice Control) :
    ShuffleOp(OK_Mux), Choices(Choices), Control(Control) {}
  llvm::ArrayRef<ShuffleOp *> getChoices() const { return Choices; }
};

class Slice : public ShuffleOp {
  InputSlice S;
public:
  Slice(InputSlice S) : ShuffleOp(OK_Slice), S(S) {}
  InputSlice getSlice() const { return S; }
};
///////////////////// END SHUFFLE OPS ///////////////////

// interface describing a shuffling/swizzling operation
struct Shuffle {
  virtual AbstractShuffleOutput getAbstractOutput(unsigned OutputId) const = 0;
  // Check if can precisely implement this shuffling task
  virtual bool canImplement(const ShuffleTask &) const = 0;
  // emit code that implements a task
  virtual bool emit(const ShuffleTask &, std::vector<VectorPack> &Emitted) const = 0;
};

#endif
