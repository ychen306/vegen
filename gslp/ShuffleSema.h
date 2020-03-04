#ifndef SHUFFLE_SEMA_H
#define SHUFFLE_SEMA_H

#include "InstSema.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/Casting.h"
#include <vector>

namespace llvm {
class OrderedInstructions;
}

// See if two interval intersects
// https://stackoverflow.com/questions/325933
static inline bool intersects(unsigned Lo1, unsigned Hi1, unsigned Lo2,
                              unsigned Hi2) {
  return Lo1 < Hi2 && Lo2 < Hi1;
}

class VectorPack {
  unsigned ElementWidth; /* unit = bits */
  std::vector<llvm::Value *> Content;
  llvm::Value *PackedContent;

public:
  VectorPack(unsigned ElementWidth, std::vector<llvm::Value *> Content,
             llvm::Value *PackedContent = nullptr)
      : ElementWidth(ElementWidth), Content(Content),
        PackedContent(PackedContent) {}
  unsigned getElementWidth() const { return ElementWidth; }
  unsigned getNumElements() const { return Content.size(); }
  llvm::ArrayRef<llvm::Value *> getContent() const { return Content; }
  llvm::Value *getPackedContent() const { return PackedContent; }
};

struct SwizzleTask {
  std::vector<VectorPack> Inputs, Outputs;
  llvm::LLVMContext &getContext() const {
    return Inputs[0].getContent()[0]->getContext();
  }
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

// Utility interface for emitting swizzle instructions.
class SwizzleValue;
// Environment for codegen
using SwizzleEnv = llvm::DenseMap<const SwizzleValue *, llvm::Value *>;

class SwizzleValue {
  unsigned Size;

public:
  SwizzleValue(unsigned Size) : Size(Size) {}
  unsigned getSize() const { return Size; }

  virtual llvm::Value *emit(SwizzleEnv &Env, IntrinsicBuilder &,
                            const llvm::OrderedInstructions *) const {
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
  SwizzleInst(unsigned Size, std::string Name,
              std::vector<SwizzleValue *> Operands, int ParamId = -1,
              bool ParamIsImm = false)
      : SwizzleValue(Size), Name(Name), Operands(Operands), ParamId(ParamId),
        ParamIsImm(ParamIsImm) {}
  llvm::Value *emit(SwizzleEnv &Env, IntrinsicBuilder &Builder,
                    const llvm::OrderedInstructions *) const override;
  SwizzleValue *getParameter() const override {
    assert(ParamId >= 0);
    return Operands[ParamId];
  }
  llvm::ArrayRef<SwizzleValue *> getOperands() const override {
    return Operands;
  }
};

///////////////////////// BEGIN SHUFFLE OPS ///////////////
// Building blocks for defining a swizzling operation
//  | DymamicSlice (base, idx, stride)
//  | Mux (ctrl : slice) (mapping number -> Slice)
//  | Slice
//  | Concat (list of values)
class SwizzleOp {
public:
  enum OpKind { OK_Input, OK_DynamicSlice, OK_Mux, OK_Slice, OK_Concat };

private:
  const OpKind Kind;
  unsigned Size;

public:
  SwizzleOp(OpKind Kind, unsigned Size) : Kind(Kind), Size(Size) {}
  OpKind getKind() const { return Kind; }
  unsigned getSize() const { return Size; }
};

class SwizzleInput : public SwizzleOp {
  const SwizzleValue *X;

public:
  SwizzleInput(const SwizzleValue *X)
      : SwizzleOp(OK_Input, X->getSize()), X(X) {}

  const SwizzleValue *get() const { return X; }

  static bool classof(const SwizzleOp *op) { return op->getKind() == OK_Input; }
};

class SwizzleValue;

class Slice : public SwizzleOp {
  const SwizzleOp *Base;
  unsigned Lo, Hi;

public:
  Slice(const SwizzleOp *Base, unsigned Lo, unsigned Hi)
      : SwizzleOp(OK_Slice, Hi - Lo), Base(Base), Lo(Lo), Hi(Hi) {}
  const SwizzleOp *getBase() const { return Base; }
  unsigned getLow() const { return Lo; }
  unsigned getHigh() const { return Hi; }
  bool intersectWith(const Slice &Other) const {
    auto *Base = llvm::cast<SwizzleInput>(this->Base)->get();
    auto *OtherBase = llvm::cast<SwizzleInput>(Other.Base)->get();
    return Base == OtherBase && intersects(Lo, Hi, Other.Lo, Other.Hi);
  }

  static bool classof(const SwizzleOp *op) { return op->getKind() == OK_Slice; }
};

class Mux : public SwizzleOp {
  std::vector<SwizzleOp *> Choices;
  const Slice *Control;

public:
  Mux(std::vector<SwizzleOp *> Choices, const Slice *Control)
      : SwizzleOp(OK_Mux, Choices[0]->getSize()), Choices(Choices),
        Control(Control) {
    assert(Choices.size() > 0 && "Empty Mux!");
    unsigned Size = Choices[0]->getSize();
    for (auto *Choice : Choices) {
      assert(Choice->getSize() == Size && "Non-uniform sizes for mux");
    }
  }
  llvm::ArrayRef<SwizzleOp *> getChoices() const { return Choices; }
  const Slice *getControl() const { return Control; }

  static bool classof(const SwizzleOp *Op) { return Op->getKind() == OK_Mux; }
};

class DynamicSlice : public SwizzleOp {
  const SwizzleOp *Base;
  unsigned Stride;
  const Slice *Index;

public:
  DynamicSlice(const SwizzleOp *Base, unsigned Stride, const Slice *Index)
      : SwizzleOp(OK_DynamicSlice, Stride), Base(Base), Stride(Stride),
        Index(Index) {}
  const SwizzleOp *getBase() const { return Base; }
  unsigned getStride() const { return Stride; }
  const Slice *getIndex() const { return Index; }

  static bool classof(const SwizzleOp *Op) {
    return Op->getKind() == OK_DynamicSlice;
  }
};

class Concat : public SwizzleOp {
  std::vector<const SwizzleOp *> Elements;
  static unsigned getTotalSize(const std::vector<const SwizzleOp *> &Elements) {
    unsigned TotalSize = 0;
    for (auto *Op : Elements)
      TotalSize += Op->getSize();
    return TotalSize;
  }

public:
  Concat(std::vector<const SwizzleOp *> Elements)
      : SwizzleOp(OK_Concat, getTotalSize(Elements)), Elements(Elements) {}
  llvm::ArrayRef<const SwizzleOp *> getElements() const { return Elements; }
  static bool classof(const SwizzleOp *Op) {
    return Op->getKind() == OK_Concat;
  }
};

///////////////////// END SHUFFLE OPS ///////////////////

// Interface describing a (parametrized) shuffling/swizzling operation
class Swizzle {
public:
private:
  InstSignature Sig;
  // The semantics tells us how to solve for the swizzle parameters
  std::vector<const SwizzleOp *> OutputSema;
  std::vector<const SwizzleValue *> Inputs;
  std::vector<const SwizzleValue *> Outputs;
  // Imprecise semantics of this swizzle; used for indexing
  std::vector<AbstractSwizzleOutput> AbstractOutputs;
  // Set of parameters we need to solve in order to implement a concrete swizzle
  // task
  llvm::DenseSet<const SwizzleValue *> ParameterSet;

public:
  Swizzle(InstSignature Sig, std::vector<const SwizzleOp *> OutputSema,
          std::vector<const SwizzleValue *> Inputs,
          std::vector<const SwizzleValue *> Outputs,
          std::vector<AbstractSwizzleOutput> AbstractOutputs);

  AbstractSwizzleOutput getAbstractOutput(unsigned OutputId) const {
    return AbstractOutputs[OutputId];
  }

  const InstSignature &getSignature() { return Sig; }

  // Try to solve the parameter required to implement this task,
  // return if it's sucessful
  bool solve(const SwizzleTask &Task, SwizzleEnv &Env,
             const llvm::OrderedInstructions *) const;

  // Emit code to implement a task
  std::vector<llvm::Value *> emit(SwizzleEnv &Env, IntrinsicBuilder &Builder,
                                  const llvm::OrderedInstructions *) const;
};

class ParameterUpdate {
  llvm::Optional<Slice> TempSlice;
  const Slice *LHS;
  unsigned RHS;

  void verify() const {
    assert(llvm::isa<SwizzleInput>(LHS->getBase()));
    assert(LHS->getSize() <= 32 && "Assignment bitwidth too large");
  }

public:
  ParameterUpdate(const Slice *LHS, unsigned RHS) : LHS(LHS), RHS(RHS) {
    verify();
  }

  ParameterUpdate(const SwizzleInput *X, unsigned RHS)
    : TempSlice(Slice(X, 0, X->getSize())), LHS(TempSlice.getPointer()), RHS(RHS) {
      verify();
  }

  bool compatibleWith(const ParameterUpdate &Other) const;

  const Slice *getLHS() const { return LHS; }
  unsigned getRHS() const { return RHS; }
};

class ParameterMap {
  // mapping <parameters> -> <their bitvector representations>
  llvm::DenseMap<const SwizzleValue *, llvm::BitVector> BVs;

public:
  ParameterMap(const llvm::DenseSet<const SwizzleValue *> &Parameters);
  void update(const ParameterUpdate &Update);
  const llvm::BitVector &get(const SwizzleValue *Param) const {
    auto It = BVs.find(Param);
    assert(It != BVs.end() && "Unknown parameter");
    return It->second;
  }
};

#endif