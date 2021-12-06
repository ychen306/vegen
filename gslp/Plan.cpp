#include "Plan.h"
#include "Heuristic.h"
#include "Packer.h"
#include "Solver.h"
#include "VectorPack.h"
#include "VectorPackContext.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Support/CommandLine.h"

using namespace llvm;

static cl::opt<bool>
    EnableCostVerification("verify-costs",
                           cl::desc("verify cost during vector planning"),
                           cl::init(false));

Plan::Plan(Packer *Pkr) : Pkr(Pkr), Cost(0) {
  for (auto &I : instructions(Pkr->getFunction())) {
    NumScalarUses[&I] = I.getNumUses();
    if (isAlive(&I))
      Cost += Pkr->getScalarCost(&I);
  }
}

void Plan::incScalarUses(Instruction *I) {
  auto It = InstToPackMap.find(I);
  bool NeedToExtract = !NumScalarUses[I] && It != InstToPackMap.end();
  // Pay the extract cost if I is packed
  if (!NumScalarUses[I] && It != InstToPackMap.end() &&
      !It->second.VP->isReduction()) {
    assert(!ExtractCosts.count(I));
    const VectorPackSlot &Slot = It->second;
    auto *VecTy = getVectorType(*Slot.VP);
    float ExtractCost = Pkr->getTTI()->getVectorInstrCost(
        Instruction::ExtractElement, VecTy, Slot.i);
    ExtractCosts[I] = ExtractCost;
    Cost += ExtractCost;
  }
  bool WasDead = !isAlive(I);
  ++NumScalarUses[I];
  if (WasDead && isAlive(I) && !getProducer(I))
    revive(I);
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
    if (auto *I = dyn_cast_or_null<Instruction>(V)) {
      if (auto *VP = getProducer(I)) {
        // I is produced by a pack we've never seen, shuffle!
        if (Gathered.insert(VP).second)
          ShuffleCost += C_Shuffle;
      } else {
        // I not produced as in a vector, insert!
        ShuffleCost +=
            TTI->getVectorInstrCost(Instruction::InsertElement, VecTy, i);
      }
    } else if (V && !isa<Constant>(V)) {
      // Not an internal instruction, insert!
      ShuffleCost +=
          TTI->getVectorInstrCost(Instruction::InsertElement, VecTy, i);
    }
  }
  return ShuffleCost;
}

void Plan::updateCostOfVectorUses(ArrayRef<Value *> Values) {
  SmallPtrSet<const OperandPack *, 4> Uses;
  for (auto *V : Values)
    if (auto *I = dyn_cast_or_null<Instruction>(V))
      for (auto *OP : InstToOperandsMap.lookup(I))
        Uses.insert(OP);
  for (auto *OP : Uses) {
    assert(NumVectorUses.lookup(OP));
    assert(ShuffleCosts.count(OP));
    float ShuffleCost = computeShuffleCost(OP);
    Cost += ShuffleCost - ShuffleCosts[OP], ShuffleCosts[OP] = ShuffleCost;
  }
}

void Plan::incVectorUses(const OperandPack *OP) {
  if (NumVectorUses[OP]++)
    return;

  float ShuffleCost = computeShuffleCost(OP);
  ShuffleCosts[OP] = ShuffleCost;
  Cost += ShuffleCost;

  // Also build the index that maps elements of
  // the vector to the vector itself
  for (auto *V : *OP)
    if (auto *I = dyn_cast_or_null<Instruction>(V)) {
      bool WasDead = !isAlive(I);
      InstToOperandsMap[I].insert(OP);
      if (isAlive(I) && WasDead && !getProducer(I))
        revive(I);
    }
}

bool Plan::isAlive(llvm::Instruction *I) const {
  return isa<ReturnInst>(I) || isa<StoreInst>(I) || isa<CallInst>(I) ||
         isa<InvokeInst>(I) || NumScalarUses.lookup(I) ||
         !InstToOperandsMap.lookup(I).empty();
}

void Plan::decVectorUses(const OperandPack *OP) {
  assert(NumVectorUses[OP] > 0);
  if (--NumVectorUses[OP])
    return;
  // OP is dead because it has zero uses
  SmallPtrSet<Instruction *, 8> Visited;
  for (auto *V : *OP)
    if (auto *I = dyn_cast_or_null<Instruction>(V)) {
      bool Inserted = Visited.insert(I).second;
      if (!Inserted)
        continue;
      assert(InstToOperandsMap.lookup(I).count(OP));
      InstToOperandsMap[I].erase(OP);
      if (!isAlive(I))
        kill(I);
    }
  NumVectorUses.erase(OP);
  assert(ShuffleCosts.count(OP));
  // Deduct the shuffle cost because we don't need to shuffle anymore
  float ShuffleCost = ShuffleCosts.lookup(OP);
  ShuffleCosts.erase(OP);
  Cost -= ShuffleCost;
}

void Plan::revive(Instruction *I) {
  assert(!getProducer(I));
  // reviving a dead instruction as scalar
  Cost += Pkr->getScalarCost(I);
  for (Value *O : I->operands())
    if (auto *I2 = dyn_cast<Instruction>(O)) {
      incScalarUses(I2);
    }
}

void Plan::kill(Instruction *I) {
  if (auto *VP = getProducer(I)) {
    bool AllDead = true;
    for (auto *V : VP->elementValues())
      if (isAlive(dyn_cast<Instruction>(V))) {
        AllDead = false;
        break;
      }
    if (AllDead)
      removeImpl(VP);
  } else {
    Cost -= Pkr->getScalarCost(I);
    for (Value *O : I->operands())
      if (auto *I2 = dyn_cast<Instruction>(O))
        decScalarUses(I2);
  }
}

void Plan::decScalarUses(Instruction *I) {
  assert(NumScalarUses[I] > 0);
  --NumScalarUses[I];

  // There's no scalar uses anymore, so deduct the extraction cost
  if (!NumScalarUses[I] && ExtractCosts.count(I)) {
    Cost -= ExtractCosts[I];
    ExtractCosts.erase(I);
  }

  if (!isAlive(I))
    kill(I);
}

bool Plan::verifyCost() const {
  if (!EnableCostVerification)
    return true;

  float TotalExtractCost = 0;
  for (auto KV : ExtractCosts) {
    Instruction *I = KV.first;
    float ExtractCost = KV.second;
    assert(getProducer(I) && isAlive(I));
    TotalExtractCost += ExtractCost;
  }
  float TotalShuffleCost = 0;
  for (auto KV : ShuffleCosts) {
    const OperandPack *OP = KV.first;
    float ShuffleCost = KV.second;
    assert(NumVectorUses.lookup(OP));
    TotalShuffleCost += ShuffleCost;
  }
  float TotalScalarCost = 0;
  for (auto &I : instructions(Pkr->getFunction()))
    if (isAlive(&I) && !getProducer(&I))
      TotalScalarCost += Pkr->getScalarCost(&I);

  float TotalVectorCost = 0;
  for (auto *VP : Packs)
    TotalVectorCost += VP->getProducingCost();
  float Cost2 =
      TotalExtractCost + TotalShuffleCost + TotalScalarCost + TotalVectorCost;
  bool Ok = Cost2 == Cost;
  if (!Ok) {
    errs() << "Cost is broken:\n\tCost = " << Cost
           << "\n\textract cost = " << TotalExtractCost
           << "\n\tshuffle cost = " << TotalShuffleCost
           << "\n\tscalar cost = " << TotalScalarCost
           << "\n\tvector cost = " << TotalVectorCost
           << "\n\trecalculated cost = " << Cost2 << '\n';
  }
  return Ok;
}

void Plan::addImpl(const VectorPack *VP) {
  Packs.insert(VP);
  Cost += VP->getProducingCost();
  for (auto *OP : VP->getOperandPacks())
    incVectorUses(OP);

  ArrayRef<Value *> Values = VP->getOrderedValues();
  ValuesToPackMap[Values] = VP;
  for (unsigned i = 0, N = Values.size(); i < N; i++) {
    if (auto *I = dyn_cast_or_null<Instruction>(Values[i])) {
      assert(!getProducer(I));
      InstToPackMap[I] = VectorPackSlot{VP, i};
    }
  }

  updateCostOfVectorUses(Values);

  auto *TTI = Pkr->getTTI();
  auto *VecTy = !VP->isStore() ? getVectorType(*VP) : nullptr;
  for (unsigned i = 0, N = Values.size(); i < N; i++)
    if (auto *I = dyn_cast_or_null<Instruction>(Values[i])) {
      if (!VP->isReduction() && NumScalarUses.lookup(I)) {
        float ExtractCost =
            TTI->getVectorInstrCost(Instruction::ExtractElement, VecTy, i);
        Cost += ExtractCost;
        ExtractCosts[I] = ExtractCost;
      }
      if (isAlive(I)) {
        Cost -= Pkr->getScalarCost(I);
        for (Value *O : I->operands())
          if (auto *I2 = dyn_cast<Instruction>(O))
            decScalarUses(I2);
      }
    }
}

void Plan::removeImpl(const VectorPack *VP) {
  assert(Packs.count(VP));
  Packs.erase(VP);
  Cost -= VP->getProducingCost();

  ArrayRef<Value *> Values = VP->getOrderedValues();
  ValuesToPackMap.erase(Values);

  for (auto *V : VP->elementValues())
    if (auto *I = dyn_cast<Instruction>(V)) {
      assert(getProducer(I) == VP);
      InstToPackMap.erase(I);
    }

  updateCostOfVectorUses(Values);

  auto *VecTy = !VP->isStore() ? getVectorType(*VP) : nullptr;
  auto *TTI = Pkr->getTTI();
  for (unsigned i = 0, N = Values.size(); i < N; i++) {
    if (auto *I = dyn_cast_or_null<Instruction>(Values[i])) {
      // If there's someone using I, we have to now produce it as a scalar
      if (isAlive(I)) {
        revive(I);
        // Since we are producing I as a scalar now, we don't need to pay the
        // extract cost One exception is "Reduction pack" which produces a
        // single scalar that we never extract
        if (!VP->isReduction() && NumScalarUses.lookup(I)) {
          assert(ExtractCosts.count(I));
          Cost -= ExtractCosts[I];
          ExtractCosts.erase(I);
        }
      }
    }
  }

  // Update the uses
  for (auto *OP : VP->getOperandPacks())
    decVectorUses(OP);
}
