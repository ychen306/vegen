#include "ShuffleSema.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/Analysis/OrderedInstructions.h"

using namespace llvm;

namespace {
// We want to create an instruction that uses a set of values,
// find out the earliest point where we can insert this instruction.
//
// In other words, find the earliest insert point that's dominated
// basic blocks of the used instructions.
IntrinsicBuilder::InsertPoint
findEarliestInsertPoint(ArrayRef<Value *> UsedValues,
                        const OrderedInstructions *OI) {
  // We only care about instructions
  std::vector<Instruction *> Insts;
  for (auto *V : UsedValues)
    if (auto *I = dyn_cast<Instruction>(V))
      Insts.push_back(I);

  auto ComesBefore = [&](Instruction *I, Instruction *J) {
    return OI->dominates(I, J);
  };
  // return the most dominated instruction
  Instruction *Latest =
      *std::max_element(Insts.begin(), Insts.end(), ComesBefore);
  BasicBlock::iterator LatestIt(Latest);
  // insert after the latest
  return IntrinsicBuilder::InsertPoint(Latest->getParent(),
                                       std::next(LatestIt));
}

// Read this as `Op[Lo : Hi] should be equivalent to Target[Lo : Hi]`.
struct Constraint {
  const SwizzleOp *Op;
  unsigned OpLo, OpHi;
  const SwizzleValue *Target;
  unsigned TargetLo, TargetHi;

  unsigned getSize() {
    return OpHi - OpLo;
  }

  // Some basic variants
  void assert_invariants() const {
    assert(OpLo < OpHi);
    assert(OpHi <= Op->getSize());
    assert(TargetLo < TargetHi);
    assert(TargetHi <= Target->getSize());
    assert(OpHi-OpLo == TargetHi-TargetLo);
  }
};

class ParameterUpdateStack {
  std::vector<ParameterUpdate> Stack;

public:
  using iterator = decltype(Stack)::iterator;
  ParameterUpdateStack() = default;
  bool try_push(ParameterUpdate Update) {
    // Verify if this update conflicts with existing updates
    for (auto &OlderUpdate : Stack)
      if (!OlderUpdate.compatibleWith(Update))
        return false;
    Stack.push_back(Update);
    return true;
  }
  void pop() { Stack.pop_back(); }
  iterator begin() { return Stack.begin(); }
  iterator end() { return Stack.end(); }
};

bool solveConstraints(std::vector<Constraint> &Cs,
                      ParameterUpdateStack &ParamUpdates) {
  // Nothing to solve
  if (Cs.empty())
    return true;

  const Constraint C = Cs.back();
  Cs.pop_back();
  C.assert_invariants();

  // enum OpKind { OK_Input, OK_DynamicSlice, OK_Mux, OK_Slice, OK_Concat };
  if (auto *X = dyn_cast<SwizzleInput>(C.Op)) {
    bool Solved = X->get() == C.Target && C.OpLo == C.TargetLo &&
                  C.OpHi == C.TargetHi && solveConstraints(Cs, ParamUpdates);
    if (Solved)
      return true;
  } else if (auto *DS = dyn_cast<DynamicSlice>(C.Op)) {
    auto *Index = DS->getIndex();
    auto *Base = DS->getBase();
    unsigned Stride = DS->getStride();
    unsigned TotalSize = DS->getBase()->getSize();
    unsigned NumChoices = TotalSize / Stride;
    for (int i = 0; i < NumChoices; i++) {
      // try this index
      bool UpdateOk = ParamUpdates.try_push(ParameterUpdate(Index, i));
      if (!UpdateOk)
        continue;
      Cs.push_back({Base, i * Stride + C.OpLo, i * Stride + Stride + C.OpHi,
                    C.Target, C.TargetLo, C.TargetHi});
      if (solveConstraints(Cs, ParamUpdates))
        return true;
      // backtrack
      Cs.pop_back();
      ParamUpdates.pop();
    }
  } else if (auto *M = dyn_cast<Mux>(C.Op)) {
    auto Choices = M->getChoices();
    unsigned NumChoices = Choices.size();
    auto *Control = M->getControl();
    for (unsigned i = 0; i < NumChoices; i++) {
      auto *Op = Choices[i];
      // try this branch
      bool UpdateOk = ParamUpdates.try_push(ParameterUpdate(Control, i));
      if (!UpdateOk)
        continue;
      Cs.push_back({Op, C.OpLo, C.OpHi, C.Target, C.TargetLo, C.TargetHi});
      if (solveConstraints(Cs, ParamUpdates))
        return true;
      // backtrack
      Cs.pop_back();
      ParamUpdates.pop();
    }
  } else if (auto *S = dyn_cast<Slice>(C.Op)) {
    unsigned NewLo = S->getLow() + C.OpLo;
    unsigned NewHi = NewLo + C.OpHi - C.OpLo;
    Cs.push_back(
        {S->getBase(), NewLo, NewHi, C.Target, C.TargetLo, C.TargetHi});
    if (solveConstraints(Cs, ParamUpdates))
      return true;
    Cs.pop_back();
  } else {
    auto *Cat = cast<Concat>(C.Op);
    unsigned Offset = 0;
    unsigned NumExtraConstraints = 0;
    // Search for concatenated elements that falls in [Lo, Hi].
    for (auto *Op : Cat->getElements()) {
      unsigned OpSize = Op->getSize();
      if (intersects(Offset, Offset + OpSize, C.OpLo, C.OpHi)) {
        unsigned IntersectLo = std::max(Offset, C.OpLo);
        unsigned IntersectHi = std::min(Offset+OpSize, C.OpHi);
        unsigned NewLo = IntersectLo - Offset;
        unsigned NewHi = NewLo + IntersectHi - IntersectLo;
        // increment the target lo by the amount we shift OpLo up
        unsigned NewTargetLo = C.TargetLo + IntersectLo - C.OpLo;
        unsigned NewTargetHi = NewTargetLo + NewHi - NewLo;
        Cs.push_back({Op, NewLo, NewHi, C.Target, NewTargetLo, NewTargetHi});
        NumExtraConstraints += 1;
      }
      Offset += OpSize;
    }
    if (solveConstraints(Cs, ParamUpdates))
      return true;
    // Failed. Remove the extra constraints we generated for this concat
    while (NumExtraConstraints--)
      Cs.pop_back();
  }

  // If we get here, we failed. Backtrack!
  Cs.push_back(C);
  return false;
}


// emit llvm representation of a bitvector
Constant *emitParameter(llvm::LLVMContext &Ctx, const BitVector &BV) {
  return nullptr;
}

} // end anonymous namespace

ParameterMap::ParameterMap(const DenseSet<const SwizzleValue *> &Parameters) {
  for (auto *Param : Parameters)
    BVs[Param] = BitVector(Param->getSize());
}

void ParameterMap::update(const ParameterUpdate &Update) {
  const Slice *LHS = Update.getLHS();
  unsigned N = LHS->getSize();
  unsigned Start = LHS->getLow();
  unsigned Val = Update.getRHS();
  const SwizzleValue *Param = cast<SwizzleInput>(LHS->getBase())->get();
  auto It = BVs.find(Param);
  assert(It != BVs.end());
  auto &Bits = It->second;
  for (unsigned i = 0; i < N; i++) {
    Bits[i + Start] = Val % 2;
    Val >>= 1;
  }
  assert(Val == 0 && "Udpate value larger than update bitwidth");
}

bool ParameterUpdate::compatibleWith(const ParameterUpdate &Other) const {
  // no conflict if the assignment doesn't touch the same values
  if (!LHS->intersectWith(*Other.LHS))
    return true;
  uint64_t V1 = RHS;
  uint64_t V2 = Other.RHS;
  // Align the RHSs
  int LowDiff = int(Other.LHS->getLow()) - int(LHS->getLow());
  // Bump up bits starting at a lower interval
  if (LowDiff > 0) {
    V2 <<= LowDiff;
  } else {
    V1 <<= -LowDiff;
  }
  // Only check the intersected bits
  uint64_t NumBits = (
      std::min(LHS->getHigh(), Other.LHS->getHigh()) -
      std::max(LHS->getLow(), Other.LHS->getLow()));
  NumBits <<= std::abs(LowDiff);
  uint64_t Mask = (1 << uint64_t(NumBits)) - 1;
  return (Mask & V1) == (Mask & V2);
}


Value *SwizzleInst::emit(SwizzleEnv &Env, IntrinsicBuilder &Builder,
                         const OrderedInstructions *OI) const {
  using ValuePtr = Value *;
  ValuePtr &V = Env[this];
  if (V != nullptr)
    return V;
  std::vector<Value *> Args;
  for (auto *Operand : Operands)
    Args.push_back(Operand->emit(Env, Builder, OI));
  auto IP = findEarliestInsertPoint(Args, OI);
  Builder.SetInsertPoint(IP.getBlock(), IP.getPoint());
  V = Builder.Create(Name, Args);
  return V;
}

Swizzle::Swizzle(InstSignature Sig, std::vector<const SwizzleOp *> OutputSema,
                 std::vector<const SwizzleValue *> Inputs,
                 std::vector<const SwizzleValue *> Outputs,
                 std::vector<AbstractSwizzleOutput> AbstractOutputs)
    : Sig(Sig), OutputSema(OutputSema), Inputs(Inputs), Outputs(Outputs),
      AbstractOutputs(AbstractOutputs) {
  unsigned NumOutputs = Sig.numOutputs();
  assert(NumOutputs == OutputSema.size() && NumOutputs == Outputs.size() &&
         NumOutputs == AbstractOutputs.size());

  // Collect the set of parameters
  std::vector<const SwizzleValue *> Worklist;
  DenseSet<const SwizzleValue *> Visited;
  while (!Worklist.empty()) {
    auto *SV = Worklist.back();
    Worklist.pop_back();

    bool Inserted = Visited.insert(SV).second;
    if (!Inserted)
      continue;

    if (auto *Param = SV->getParameter())
      ParameterSet.insert(Param);

    for (auto *Operand : SV->getOperands())
      Worklist.push_back(Operand);
  }
}

// TODO: use the abstract output to guide solving.
bool Swizzle::solve(const SwizzleTask &Task, SwizzleEnv &Env,
                    const OrderedInstructions *OI) const {
  struct SwizzleValueSlice {
    const SwizzleValue *SV;
    unsigned Lo, Hi;
  };
  // bind input value of this task to a slice of the input swizzle values
  DenseMap<const Value *, SwizzleValueSlice> InputValueMap;
  unsigned NumInputs = Task.Inputs.size();
  assert(NumInputs == Inputs.size());
  for (unsigned i = 0; i < NumInputs; i++) {
    const auto &Pack = Task.Inputs[i];
    const auto &SV = Inputs[i];
    unsigned j = 0;
    unsigned ElemSize = Pack.getElementWidth();
    for (auto *X : Pack.getContent()) {
      InputValueMap[X] =
          SwizzleValueSlice{SV, j * ElemSize, j * ElemSize + ElemSize};
      j += 1;
    }
  }

  // Generate all of the initial constraints
  std::vector<Constraint> Constraints;
  unsigned NumOutputs = OutputSema.size();
  for (unsigned i = 0; i < NumOutputs; i++) {
    const SwizzleOp *OutputOp = OutputSema[i];
    auto &OutputPack = Task.Outputs[i];
    unsigned ElemSize = OutputPack.getElementWidth();

    unsigned j = 0;
    for (const Value *Y : OutputPack.getContent()) {
      auto &TargetSlice = InputValueMap[Y];
      Constraints.push_back({OutputOp, j * ElemSize, j * ElemSize + ElemSize,
                             // Target
                             TargetSlice.SV, TargetSlice.Lo, TargetSlice.Hi});
      j += 1;
    }
  }

  ParameterUpdateStack ParamUpdates;
  unsigned Solved = solveConstraints(Constraints, ParamUpdates);
  if (!Solved)
    return false;
  ParameterMap Params(ParameterSet);
  for (auto &Update : ParamUpdates)
    Params.update(Update);

  // Emit and bind the solved parameters
  auto &Ctx = Task.getContext();
  for (const SwizzleValue *Param : ParameterSet) {
    Env[Param] = emitParameter(Ctx, Params.get(Param));
  }

  // Bind the input
  for (unsigned i = 0; i < NumInputs; i++) {
    Value *X = Task.Inputs[i].getPackedContent();
    assert(X && "Input not packed");
    Env[Inputs[i]] = X;
  }
  
  // TODO: verify all of the instructions used inside this swizzle kernel
  // can be produced before they are needed
  return true;
}

std::vector<Value *> Swizzle::emit(SwizzleEnv &Env, IntrinsicBuilder &Builder,
                                   const OrderedInstructions *OI) const {
  std::vector<Value *> Emitted;
  for (auto *Y : Outputs)
    Emitted.push_back(Y->emit(Env, Builder, OI));
  return Emitted;
}
