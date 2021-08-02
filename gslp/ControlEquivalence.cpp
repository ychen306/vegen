// This largely a copy-pasted impl of llvm::isControlFlowEquivalent.
// We modify it so that ControlCondition::isEquivalent tries harder.
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Instructions.h"

using namespace llvm;

namespace {
// Copy from llvm/lib/Transforms/Utils/CodeMoveUtils.cpp
using ControlCondition = PointerIntPair<Value *, 1, bool>;

/// Represent a set of control conditions required to execute ToBB from FromBB.
class ControlConditions {
  using ConditionVectorTy = SmallVector<ControlCondition, 6>;

  /// A SmallVector of control conditions.
  ConditionVectorTy Conditions;

public:
  /// Return a ControlConditions which stores all conditions required to execute
  /// \p BB from \p Dominator. If \p MaxLookup is non-zero, it limits the
  /// number of conditions to collect. Return None if not all conditions are
  /// collected successfully, or we hit the limit.
  static const Optional<ControlConditions>
  collectControlConditions(const BasicBlock &BB, const BasicBlock &Dominator,
                           const DominatorTree &DT,
                           const PostDominatorTree &PDT,
                           unsigned MaxLookup = 6);

  /// Return true if there exists no control conditions required to execute ToBB
  /// from FromBB.
  bool isUnconditional() const { return Conditions.empty(); }

  /// Return a constant reference of Conditions.
  const ConditionVectorTy &getControlConditions() const { return Conditions; }

  /// Add \p V as one of the ControlCondition in Condition with IsTrueCondition
  /// equals to \p True. Return true if inserted successfully.
  bool addControlCondition(ControlCondition C);

  /// Return true if for all control conditions in Conditions, there exists an
  /// equivalent control condition in \p Other.Conditions.
  bool isEquivalent(const ControlConditions &Other) const;

  /// Return true if \p C1 and \p C2 are equivalent.
  static bool isEquivalent(const ControlCondition &C1,
                           const ControlCondition &C2);

private:
  ControlConditions() = default;

  static bool isEquivalent(const Value &V1, const Value &V2);
  static bool isInverse(const Value &V1, const Value &V2);
};
} // namespace

const Optional<ControlConditions> ControlConditions::collectControlConditions(
    const BasicBlock &BB, const BasicBlock &Dominator, const DominatorTree &DT,
    const PostDominatorTree &PDT, unsigned MaxLookup) {
  assert(DT.dominates(&Dominator, &BB) && "Expecting Dominator to dominate BB");

  ControlConditions Conditions;
  unsigned NumConditions = 0;

  // BB is executed unconditional from itself.
  if (&Dominator == &BB)
    return Conditions;

  const BasicBlock *CurBlock = &BB;
  // Walk up the dominator tree from the associated DT node for BB to the
  // associated DT node for Dominator.
  do {
    assert(DT.getNode(CurBlock) && "Expecting a valid DT node for CurBlock");
    BasicBlock *IDom = DT.getNode(CurBlock)->getIDom()->getBlock();
    assert(DT.dominates(&Dominator, IDom) &&
           "Expecting Dominator to dominate IDom");

    // Limitation: can only handle branch instruction currently.
    const BranchInst *BI = dyn_cast<BranchInst>(IDom->getTerminator());
    if (!BI)
      return None;

    bool Inserted = false;
    if (PDT.dominates(CurBlock, IDom)) {
    } else if (PDT.dominates(CurBlock, BI->getSuccessor(0))) {
      Inserted = Conditions.addControlCondition(
          ControlCondition(BI->getCondition(), true));
    } else if (PDT.dominates(CurBlock, BI->getSuccessor(1))) {
      Inserted = Conditions.addControlCondition(
          ControlCondition(BI->getCondition(), false));
    } else
      return None;

    if (Inserted)
      ++NumConditions;

    if (MaxLookup != 0 && NumConditions > MaxLookup)
      return None;

    CurBlock = IDom;
  } while (CurBlock != &Dominator);

  return Conditions;
}

bool ControlConditions::addControlCondition(ControlCondition C) {
  bool Inserted = false;
  if (none_of(Conditions, [&](ControlCondition &Exists) {
        return ControlConditions::isEquivalent(C, Exists);
      })) {
    Conditions.push_back(C);
    Inserted = true;
  }

  return Inserted;
}

bool ControlConditions::isEquivalent(const ControlConditions &Other) const {
  if (Conditions.empty() && Other.Conditions.empty())
    return true;

  if (Conditions.size() != Other.Conditions.size())
    return false;

  return all_of(Conditions, [&](const ControlCondition &C) {
    return any_of(Other.Conditions, [&](const ControlCondition &OtherC) {
      return ControlConditions::isEquivalent(C, OtherC);
    });
  });
}

bool ControlConditions::isEquivalent(const ControlCondition &C1,
                                     const ControlCondition &C2) {
  if (C1.getInt() == C2.getInt()) {
    if (isEquivalent(*C1.getPointer(), *C2.getPointer()))
      return true;
  } else if (isInverse(*C1.getPointer(), *C2.getPointer()))
    return true;

  return false;
}

bool ControlConditions::isEquivalent(const Value &V1, const Value &V2) {
  if (&V1 == &V2)
    return true;
  auto *I1 = dyn_cast<Instruction>(&V1);
  auto *I2 = dyn_cast<Instruction>(&V2);
  if (!I1 || !I2 || I1->getOpcode() != I2->getOpcode() ||
      I1->getNumOperands() != I2->getNumOperands())
    return false;

  // Don't even bother looking past phi node
  if (isa<PHINode>(I1))
    return false;

  for (unsigned i = 0; i < I1->getNumOperands(); i++)
    if (!isEquivalent(*I1->getOperand(i), *I2->getOperand(i)))
      return false;
  return true;
}

bool ControlConditions::isInverse(const Value &V1, const Value &V2) {
  if (const CmpInst *Cmp1 = dyn_cast<CmpInst>(&V1))
    if (const CmpInst *Cmp2 = dyn_cast<CmpInst>(&V2)) {
      if (Cmp1->getPredicate() == Cmp2->getInversePredicate() &&
          Cmp1->getOperand(0) == Cmp2->getOperand(0) &&
          Cmp1->getOperand(1) == Cmp2->getOperand(1))
        return true;

      if (Cmp1->getPredicate() ==
              CmpInst::getSwappedPredicate(Cmp2->getInversePredicate()) &&
          Cmp1->getOperand(0) == Cmp2->getOperand(1) &&
          Cmp1->getOperand(1) == Cmp2->getOperand(0))
        return true;
    }
  return false;
}

bool isControlEquivalent(const BasicBlock &BB0, const BasicBlock &BB1,
                         const DominatorTree &DT,
                         const PostDominatorTree &PDT) {
  if (&BB0 == &BB1)
    return true;

  if ((DT.dominates(&BB0, &BB1) && PDT.dominates(&BB1, &BB0)) ||
      (PDT.dominates(&BB0, &BB1) && DT.dominates(&BB1, &BB0)))
    return true;

  // If the set of conditions required to execute BB0 and BB1 from their common
  // dominator are the same, then BB0 and BB1 are control flow equivalent.
  const BasicBlock *CommonDominator = DT.findNearestCommonDominator(&BB0, &BB1);

  const Optional<ControlConditions> BB0Conditions =
      ControlConditions::collectControlConditions(BB0, *CommonDominator, DT,
                                                  PDT);
  if (BB0Conditions == None)
    return false;

  const Optional<ControlConditions> BB1Conditions =
      ControlConditions::collectControlConditions(BB1, *CommonDominator, DT,
                                                  PDT);
  if (BB1Conditions == None)
    return false;

  return BB0Conditions->isEquivalent(*BB1Conditions);
}
