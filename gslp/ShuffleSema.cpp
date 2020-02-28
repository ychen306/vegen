#include "ShuffleSema.h"

using namespace llvm;

Value *SwizzleInst::emit(SwizzleEnv &Env, IntrinsicBuilder &Builder) const {
  using ValuePtr = Value *;
  ValuePtr &V = Env[this];
  if (V != nullptr)
    return V;
  std::vector<Value *> Args;
  for (auto *Operand : Operands)
    Args.push_back(Operand->emit(Env, Builder));
  V = Builder.Create(Name, Args);
  return V;
}

Swizzle::Swizzle(InstSignature Sig, std::vector<VectorSemantics> Semantics,
                 std::vector<const SwizzleValue *> Inputs,
                 std::vector<const SwizzleValue *> Outputs,
                 std::vector<AbstractSwizzleOutput> AbstractOutputs)
    : Sig(Sig), Semantics(Semantics), Inputs(Inputs), Outputs(Outputs),
      AbstractOutputs(AbstractOutputs) {
  unsigned NumOutputs = Sig.numOutputs();
  assert(NumOutputs == Semantics.size() && NumOutputs == Outputs.size() &&
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

bool Swizzle::solveForParameter(const SwizzleTask &Task,
                                ParameterMap &Parameters) const {}
