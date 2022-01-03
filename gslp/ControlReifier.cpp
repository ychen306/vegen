#include "ControlReifier.h"
#include "ControlDependence.h"
#include "DependenceAnalysis.h"
#include "VLoop.h"
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
  auto *And = dyn_cast<ConditionAnd>(C);
  if (And) {
    reify(And->Parent, VL);

    Value *Cond = And->Cond;
    if (!And->IsTrue) {
      auto *Not = BinaryOperator::CreateNot(Cond);
      InsertedInsts.push_back(Not);
      VL->addInstruction(Not, And->Parent);
      Cond = Not;
    }

    Reified = VL->createOneHotPhi(And->Parent, Cond, ConstantInt::getFalse(Ctx),
                                  "reified.onehot");
  } else {
    auto *Or = dyn_cast<ConditionOr>(C);
    Reified = reify(Or->Conds.front(), VL);
    for (auto *C2 : drop_begin(Or->Conds)) {
      auto *Tmp = BinaryOperator::CreateOr(Reified, reify(C2, VL));
      InsertedInsts.push_back(Tmp);
      VL->addInstruction(Tmp, nullptr);
      Reified = Tmp;
    }
  }
  assert(Reified);

  ReifiedValues[{C, VL}] = Reified;
  if (And)
    reify(And->Complement, VL);

  return Reified;
}

bool ControlReifier::hasValue(const ControlCondition *C, VLoop *VL) {
  return !C || ReifiedValues.count({C, VL});
}

Value *ControlReifier::getValue(const ControlCondition *C, VLoop *VL) {
  assert(hasValue(C, VL));
  if (!C)
    return ConstantInt::getTrue(Ctx);
  return ReifiedValues.lookup({C, VL});
}
