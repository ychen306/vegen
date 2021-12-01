#include "DependenceAnalysis.h"
#include "VLoop.h"
#include "ControlReifier.h"
#include "ControlDependence.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"

using namespace llvm;

Value *ControlReifier::reify(const ControlCondition *C, VLoop *VL) {
  if (!C)
    return ConstantInt::getTrue(Ctx);

  auto It = ReifiedValues.find({C, VL});
  if (It != ReifiedValues.end())
    return It->second;

  Value *Reified = nullptr;
  if (auto *And = dyn_cast<ConditionAnd>(C)) {
    reify(And->Parent, VL);

    Value *Cond = And->Cond;
    if (!And->IsTrue) {
      auto *Not = BinaryOperator::CreateNot(Cond);
      VL->addInstruction(Not, And->Parent);
      DA.addInstruction(Not);
      Cond = Not;
    }

    auto *Phi = VL->createOneHotPhi(And->Parent, Cond, ConstantInt::getFalse(Ctx));
    DA.addInstruction(Phi);
    Reified = Phi;
  } else {
    auto *Or = dyn_cast<ConditionOr>(C);
    Reified = reify(Or->Conds.front(), VL);
    for (auto *C2 : drop_begin(Or->Conds)) {
      auto *Tmp = BinaryOperator::CreateOr(Reified, reify(C2, VL));
      VL->addInstruction(Tmp, nullptr);
      DA.addInstruction(Tmp);
      Reified = Tmp;
    }
  }
  assert(Reified);

  return ReifiedValues[{C,VL}] = Reified;
}

void ControlReifier::reifyConditionsInLoop(VLoop *VL) {
  for (auto *I : VL->getInstructions())
    reify(VL->getInstCond(I), VL);
  for (auto &SubVL : VL->getSubLoops())
    reify(SubVL->getLoopCond(), VL);
}

Value *ControlReifier::getValue(const ControlCondition *C, VLoop *VL) {
  assert(ReifiedValues.count({C, VL}));
  return ReifiedValues.lookup({C, VL});
}
