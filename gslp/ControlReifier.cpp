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
                                  "reified");
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

void ControlReifier::reifyConditionsInLoop(VLoop *VL) {
  SmallVector<Instruction *> Insts(VL->inst_begin(), VL->inst_end());
  for (auto *I : Insts) {
    reify(VL->getInstCond(I), VL);
    auto *PN = dyn_cast<PHINode>(I);
    if (!PN)
      continue;

    // Reify the condition of a one-hot phi
    if (auto OneHot = VL->getOneHotPhi(PN))
      reify(OneHot->C, VL);

    if (!VL->isGatedPhi(PN))
      continue;

    // Reify the conditions of a gated phi
    for (unsigned i = 0; i < PN->getNumIncomingValues(); i++)
      reify(VL->getIncomingPhiCondition(PN, i), VL);
  }
  for (auto &SubVL : VL->getSubLoops())
    reify(SubVL->getLoopCond(), VL);
  reify(VL->getBackEdgeCond(), VL);
}

Value *ControlReifier::getValue(const ControlCondition *C, VLoop *VL) {
  if (!C)
    return ConstantInt::getTrue(Ctx);
  assert(ReifiedValues.count({C, VL}));
  return ReifiedValues.lookup({C, VL});
}
