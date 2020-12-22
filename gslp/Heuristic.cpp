#include "Heuristic.h"
#include "Solver.h"

using namespace llvm;

static constexpr float C_Splat = 1.0;
static constexpr float C_Insert = 0.5;
static constexpr float C_Perm = 0.5;
static constexpr float C_Shuffle = 0.5;
static constexpr float C_Extract = 0.5;

static unsigned getNumUsers(Value *V) {
  return 1;
  if (!V)
    return 0;
  return std::distance(V->user_begin(), V->user_end());
}

static unsigned getNumUsers(ArrayRef<Value *> Vals) {
  return 1;
  unsigned NumUsers = Vals.size();
  for (auto *V : Vals)
    NumUsers = std::max<unsigned>(NumUsers, getNumUsers(V));
  return NumUsers;
}

static unsigned getNumUsers(const VectorPack *VP) {
  return getNumUsers(VP->getOrderedValues());
}

float Heuristic::getCost(const VectorPack *VP) {
  float Cost = VP->getProducingCost();
  for (auto *OP : VP->getOperandPacks())
    Cost += getCost(OP);
  return Cost;
}

float Heuristic::getCost(Instruction *I) {
  float Cost = Pkr->getScalarCost(I);
  for (Value *V : I->operands()) {
    Cost += getCost(V);
  }
  return Cost;
}

float Heuristic::getCost(const OperandPack *OP) {
  auto It = OrderedCosts.find(OP);
  if (It != OrderedCosts.end())
    return It->second;

  OrderedCosts[OP] = 0;
  float NumUsers = getNumUsers(*OP);

  // Build by explicit insertion
  float Cost = 0;
  for (auto *V : *OP) {
    if (!V || isa<Constant>(V))
      continue;
    Cost += getCost(V) + C_Insert / NumUsers;
  }

  // Build by broadcast
  if (is_splat(*OP)) {
    Cost = std::min(Cost, getCost((*OP)[0]) + C_Splat / NumUsers);
  }

  // Build by producer
  auto OPI = Pkr->getProducerInfo(VPCtx, OP);
  for (auto *VP : OPI.Producers)
    Cost = std::min(Cost, getCost(VP));

#if 1
  // Build by composing with other vectors
  // FIXME: deal with don't care.
  std::set<Value *> OPVals(OP->begin(), OP->end());
  if (Candidates) {
    for (auto *VP : Candidates->Packs) {
      if (!VP->getElements().anyCommon(OPI.Elements))
        continue;
      ArrayRef<Value *> Vals = VP->getOrderedValues();
      // FIXME: consider don't care
      if (Vals.size() == OP->size() &&
          std::is_permutation(Vals.begin(), Vals.end(), OP->begin())) {
        Cost = std::min(Cost, getCost(VP) + C_Perm / NumUsers);
      } else {
        BitVector Intersection = OPI.Elements;
        Intersection &= VP->getElements();
        Cost = std::min(Cost, getCost(VP) / float(Intersection.count()) *
                                      float(OPI.Elements.count()) + C_Shuffle / NumUsers);
      }
    }
  }
#endif

  OrderedCosts[OP] = Cost;
  return Cost;
}

// Vals should be sorted
float Heuristic::getCost(std::vector<Value *> Vals) {
  if (Vals.empty())
    return 0;

  auto It = UnorderedCosts.find(Vals);
  if (It != UnorderedCosts.end())
    return It->second;
  UnorderedCosts[Vals] = 0;

  float NumUsers = getNumUsers(Vals);
  assert(NumUsers > 0);

  // Build by explicit insertion
  float Cost = 0;
  for (auto *V : Vals) {
    Cost += getCost(V) + C_Insert / NumUsers;
  }

  // Build by broadcast
  if (is_splat(Vals)) {
    Cost = std::min(Cost, getCost(*Vals.begin()) + C_Splat / NumUsers);
  }

  //// Build by producer
  // auto OPI = Pkr->getProducerInfo(VPCtx, OP);
  // for (auto *VP : OPI.Producers)
  //  Cost = std::min(Cost, getCost(VP));

  // Build by composing with other vectors
  std::set<Value *> ValSet(Vals.begin(), Vals.end());
  if (Candidates) {
    BitVector Elements(VPCtx->getNumValues());
    for (auto *V : Vals) {
      if (!V)
        continue;
      auto *I = dyn_cast<Instruction>(V);
      if (I && I->getParent() == VPCtx->getBasicBlock())
        Elements.set(VPCtx->getScalarId(I));
    }
    for (auto *VP : Candidates->Packs) {
      if (!VP->getElements().anyCommon(Elements))
        continue;
      // BitVector Intersection = Elements;
      // Intersection &= VP->getElements();
      // Cost = std::min(Cost,
      //    getCost(VP) / float(Intersection.count()) * float(Elements.count())
      //  + (Intersection.count() == Elements.count() ? : 0 +
      //  C_Shuffle/NumUsers));
      ArrayRef<Value *> Outputs = VP->getOrderedValues();
      // FIXME: consider don't care
      if (Outputs.size() == Vals.size() &&
          std::is_permutation(Outputs.begin(), Outputs.end(), Vals.begin())) {
        Cost = std::min(Cost, getCost(VP));
      } else {
        std::set<Value *> Leftover = ValSet;
        for (auto *V : VP->elementValues())
          Leftover.erase(V);
        float LeftoverCost =
            getCost(std::vector<Value *>(Leftover.begin(), Leftover.end()));
        Cost =
            std::min(Cost, getCost(VP) + LeftoverCost + C_Shuffle / NumUsers);
      }
    }
  }

  return UnorderedCosts[Vals] = Cost;
}

float Heuristic::getCost(Value *V) {
  if (!V)
    return 0;
  auto *I = dyn_cast<Instruction>(V);
  if (!I || I->getParent() != VPCtx->getBasicBlock())
    return 0;

  auto It = ScalarCosts.find(I);
  if (It != ScalarCosts.end())
    return It->second;

  ScalarCosts[I] = 0;

  float Cost = getCost(I);

  float NumUsers = getNumUsers(I);

#if 0
  if (Candidates) {
    for (auto *VP : Candidates->Inst2Packs[VPCtx->getScalarId(I)]) {
      Cost = std::min(Cost, getCost(VP) + C_Extract / NumUsers);
    }
  }
#endif

  return ScalarCosts[I] = Cost;
}

// FIXME: need to estimate cost of stores, which are not explicitly live-outs
float Heuristic::getCost(const Frontier *Frt) {
  float Cost = 0;
  for (const OperandPack *OP : Frt->getUnresolvedPacks())
    Cost += getCost(OP);
  for (Value *V : Frt->getUnresolvedScalars()) {
    Cost += getCost(V);
  }
  return Cost;
}
