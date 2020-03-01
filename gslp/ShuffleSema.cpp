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

class ParameterUpdate {
  const Slice *LHS;
  unsigned RHS;

public:
  ParameterUpdate(const Slice *LHS, unsigned RHS) : LHS(LHS), RHS(RHS) {
    assert(isa<SwizzleInput>(LHS->getBase()));
    assert(LHS->getSize() <= 32 && "Assignment bitwidth too large");
  }

  bool compatibleWith(const ParameterUpdate &Other) const {
    // no conflict if the assignment doesn't touch the same values
    if (!LHS->intersectWith(*Other.LHS))
      return true;
    unsigned V1 = RHS;
    unsigned V2 = Other.RHS;
    // Align the RHSs
    int Diff = int(Other.LHS->getLow()) - int(LHS->getLow());
    // Bump down bits starting at a higher interval
    if (Diff > 0) {
      V2 >>= Diff;
    } else {
      V1 >>= -Diff;
    }
    uint64_t NumBits = std::min(LHS->getSize(), Other.LHS->getSize());
    uint64_t Mask = (1 << NumBits) - 1;
    return (Mask & V1) == (Mask & V2);
  }

  const Slice *getLHS() const { return LHS; }
  unsigned getRHS() const { return RHS; }
};

class Parameter {
  BitVector Bits;

public:
  Parameter(unsigned Size) : Bits(Size) {}
  void update(ParameterUpdate Update) {
    unsigned N = Update.getLHS()->getSize();
    unsigned Start = Update.getLHS()->getLow();
    unsigned Val = Update.getRHS();
    for (unsigned i = 0; i < N; i++) {
      Bits[i + Start] = Val % 2;
      Val >>= 1;
    }
  }

  // Emit the llvm representation for this parameter
  Constant *emit(LLVMContext &Ctx);
};

// Given a parameterized operation, solve for its parameter so that
// its value at range [Lo:hi] is equivalent to the Target
bool solve(const SwizzleOp *Op, unsigned Lo, unsigned Hi, const SwizzleValue *Target,
           std::vector<ParameterUpdate> &UpdateStack) {
  unsigned N = Hi - Lo;
  assert(N == Target->getSize());
  assert(Hi <= Op->getSize());
  if (auto *DS = dyn_cast<DynamicSlice>(Op)) {
    auto *Base = DS->getBase();
    auto *Index = DS->getIndex();
    unsigned Stride = DS->getStride();
    unsigned N = Base->getSize() / Stride;
    for (unsigned i = 0; i < N; i++) {
      UpdateStack.push_back(ParameterUpdate(Index, i));
      unsigned Offset = i * Stride;
      bool Solved = solve(Base, Offset+Lo, Offset+Hi, Target, UpdateStack);
      if (Solved)
        return true;
      UpdateStack.pop_back();
    }

    return false;
  }

//  | DymamicSlice (base, idx, stride)
//  | Mux (ctrl : slice) (mapping number -> Slice)
//  | Slice
}

} // end anonymous namespace

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
  Builder.setInsertPoint(IntrinsicBuilder::InsertPoint(IP));
  V = Builder.Create(Name, Args);
  return V;
}

Swizzle::Swizzle(InstSignature Sig,
    std::vector<SwizzleOp *> OutputSema,
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

bool Swizzle::solve(const SwizzleTask &Task, SwizzleEnv &Env,
                    const OrderedInstructions *OI) const {
  std::vector<ParameterUpdate> ParamUpdates;

  return true;
}

std::vector<Value *> Swizzle::emit(SwizzleEnv &Env, IntrinsicBuilder &Builder,
                                   const OrderedInstructions *OI) const {
  std::vector<Value *> Emitted;
  for (auto *Y : Outputs)
    Emitted.push_back(Y->emit(Env, Builder, OI));
  return Emitted;
}
