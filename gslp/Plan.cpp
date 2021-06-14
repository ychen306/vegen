#include "Plan.h"
#include "Heuristic.h"
#include "Packer.h"
#include "Solver.h"
#include "VectorPack.h"
#include "VectorPackContext.h"

using namespace llvm;

static const OperandPack *toOperandPack(const VectorPackContext *VPCtx,
                                        ArrayRef<Value *> Values) {
  OperandPack OP;
  for (auto *V : Values)
    OP.push_back(V);
  return VPCtx->getCanonicalOperandPack(OP);
}

Plan::Plan(Packer *Pkr, BasicBlock *BB) : Pkr(Pkr), BB(BB), Cost(0) {
  for (auto &I : *BB) {
    Cost += Pkr->getScalarCost(&I);
    NumUses[&I] = I.getNumUses();
  }
}

Instruction *Plan::asInternalInst(Value *V) const {
  auto *I = dyn_cast_or_null<Instruction>(V);
  if (I && I->getParent() == BB)
    return I;
  return nullptr;
}

void Plan::incUses(Instruction *I) {
  if (NumUses[I]++ > 0)
    return;

  if (InstToPackMap.lookup(I))
    return;

  // reviving a dead instruction as scalar
  Cost += Pkr->getScalarCost(I);
  for (Value *O : I->operands())
    if (auto *I2 = asInternalInst(O))
      incUses(I2);
}

void Plan::decUses(Instruction *I) {
  assert(NumUses[I] > 0);
  if (--NumUses[I] > 0)
    return;

  // `I` is now dead
  if (auto *VP = InstToPackMap.lookup(I)) {
    bool AllDead = true;
    for (auto *V : VP->elementValues()) {
      auto *I2 = dyn_cast<Instruction>(V);
      if (I2 && NumUses[I2]) {
        AllDead = false;
        break;
      }
    }
    if (AllDead)
      remove(VP);
  } else {
    Cost -= Pkr->getScalarCost(I);
    for (Value *O : I->operands())
      if (auto *I2 = asInternalInst(O))
        decUses(I2);
  }
}

float Plan::computeShuffleCost(const OperandPack *OP) const {
  constexpr float C_Shuffle = 2;
  auto *VecTy = getVectorType(*OP);
  auto *TTI = Pkr->getTTI();

  // Fast path: OP is produced exactly
  if (ValuesToPackMap.count(*OP))
    return 0;

  // Second fastest path: OP is a broadcast
  if (is_splat(*OP))
    return TTI->getShuffleCost(TargetTransformInfo::SK_Broadcast, VecTy, 0);

  float ShuffleCost = 0;

  SmallPtrSet<const VectorPack *, 4> Gathered;
  for (unsigned i = 0, N = OP->size(); i < N; i++) {
    Value *V = (*OP)[i];
    if (auto *I = asInternalInst(V)) {
      if (auto *VP = InstToPackMap.lookup(I)) {
        // I is produced by a pack we've never seen, shuffle!
        if (Gathered.insert(VP).second)
          ShuffleCost += C_Shuffle;
      } else {
        // I not produced as in a vector, insert!
        ShuffleCost += TTI->getVectorInstrCost(Instruction::InsertElement, VecTy, i);
      }
    } else if (isa_and_nonnull<Constant>(V)) {
      // Not an internal instruction, insert!
      ShuffleCost += TTI->getVectorInstrCost(Instruction::InsertElement, VecTy, i);
    }
  }
  return ShuffleCost;
}

bool Plan::hasScalarUser(Instruction *I) const {
  for (User *U : I->users()) {
    auto *I2 = asInternalInst(U);
    if (!I2 || (NumUses.lookup(I2) && !InstToPackMap.count(I2))) {
      return true;
    }
  }
  return false;
}

void Plan::updateCostOfVectorUses(ArrayRef<Value *> Values) {
  SmallPtrSet<const OperandPack *, 4> Uses;
  for (auto *V : Values)
    if (auto *I = asInternalInst(V))
      for (auto *OP : InstToOperandsMap.lookup(I))
        Uses.insert(OP);
  for (auto *OP : Uses) {
    assert(NumOperandUses.lookup(OP));
    assert(ShuffleCosts.count(OP));
    float ShuffleCost = computeShuffleCost(OP);
    Cost += ShuffleCost - ShuffleCosts[OP];
    ShuffleCosts[OP] = ShuffleCost;
  }
}

void Plan::add(const VectorPack *VP) {
  Packs.insert(VP);
  Cost += VP->getProducingCost();
  for (auto *OP : VP->getOperandPacks()) {
    if (!NumOperandUses[OP]++) {
      float ShuffleCost = computeShuffleCost(OP);
      ShuffleCosts[OP] = ShuffleCost;
      Cost += ShuffleCost;
    }
    // Update the uses
    for (auto *V : *OP)
      if (auto *I = asInternalInst(V)) {
        incUses(I);
        InstToOperandsMap[I].insert(OP);
      }
  }

  ArrayRef<Value *> Values = VP->getOrderedValues();
  ValuesToPackMap[Values] = VP;
  updateCostOfVectorUses(Values);

  FixedVectorType *VecTy = !VP->isStore() ? getVectorType(*VP) : nullptr;
  auto *TTI = Pkr->getTTI();
  for (unsigned i = 0, N = Values.size(); i < N; i++) {
    if (auto *I = dyn_cast_or_null<Instruction>(Values[i])) {
      assert(!InstToPackMap[I]);
      InstToPackMap[I] = VP;
      // We no longer produce `I` as a scalar
      if (NumUses[I]) {
        for (Value *O : I->operands())
          if (auto *I2 = asInternalInst(O))
            decUses(I2);
        Cost -= Pkr->getScalarCost(I);
        // Need to extract I if there's a scalar user
        if (hasScalarUser(I))
          Cost +=
              TTI->getVectorInstrCost(Instruction::ExtractElement, VecTy, i);
      }
      assert(NumUses[I] || !hasScalarUser(I));
    }
  }
}

// FIXME: update cost
void Plan::remove(const VectorPack *VP) {
  Packs.erase(VP);
  Cost -= VP->getProducingCost();

  ArrayRef<Value *> Values = VP->getOrderedValues();
  ValuesToPackMap.erase(Values);
  updateCostOfVectorUses(Values);

  auto *VecTy = !VP->isStore() ? getVectorType(*VP) : nullptr;
  auto *TTI = Pkr->getTTI();
  for (unsigned i = 0, N = Values.size(); i < N; i++) {
    if (auto *I = dyn_cast_or_null<Instruction>(Values[i])) {
      assert(InstToPackMap.lookup(I) == VP);
      InstToPackMap.erase(I);
      // If there's someone using I, we have to now produce it as a scalar
      if (NumUses[I]) {
        for (Value *O : I->operands())
          if (auto *I2 = asInternalInst(O))
            incUses(I2);
        Cost += Pkr->getScalarCost(I);
        // We don't need to extract `I` anymore now that it's not packed
        if (hasScalarUser(I))
          Cost -=
              TTI->getVectorInstrCost(Instruction::ExtractElement, VecTy, i);
      }
      assert(NumUses[I] || !hasScalarUser(I));
    }
  }

  // Update the uses
  for (auto *OP : VP->getOperandPacks()) {
    assert(NumOperandUses[OP] > 0);
    if (--NumOperandUses[OP])
      continue;
    // OP is dead because it has zero uses
    for (auto *V : *OP) {
      if (auto *I = asInternalInst(V)) {
        InstToOperandsMap[I].erase(OP);
        decUses(I);
      }
    }
    NumOperandUses.erase(OP);
    assert(ShuffleCosts.count(OP));
    // Deduct the shuffle cost because we don't need to shuffle anymore
    float ShuffleCost = ShuffleCosts.lookup(OP);
    ShuffleCosts.erase(OP);
    Cost -= ShuffleCost;
  }
}
