#include "Heuristic.h"
#include "Solver.h"
#include "llvm/Support/Timer.h"

using namespace llvm;

static constexpr float C_Splat = 1.0;
static constexpr float C_Insert = 2;
static constexpr float C_Perm = 0.5;
static constexpr float C_Shuffle = 0.5;
static constexpr float C_Extract = 1.0;

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

// Remove duplicate elements in OP
static const OperandPack *dedup(const VectorPackContext *VPCtx,
                                const OperandPack *OP) {
  SmallPtrSet<Value *, 4> Seen;
  OperandPack Deduped;
  for (auto *V : *OP) {
    bool Inserted = Seen.insert(V).second;
    if (!Inserted)
      continue;
    Deduped.push_back(V);
  }
  // Fast path for when we've removed nothing
  if (Deduped.size() == OP->size())
    return OP;
  return VPCtx->getCanonicalOperandPack(Deduped);
}

float Heuristic::getCost(const VectorPack *VP) {
  float Cost = VP->getProducingCost();
  for (auto *OP : VP->getOperandPacks())
    Cost += getCost(dedup(VPCtx, OP));
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

  // Build by explicit insertion
  float Cost = 0;
  for (auto *V : *OP) {
    if (!V || isa<Constant>(V))
      continue;
    Cost += getCost(V) /*/getNumUsers(V)*/ + C_Insert;
  }
  if (Cost == 0)
    return 0;

  // Build by broadcast
  if (is_splat(*OP)) {
    auto *V = (*OP)[0];
    Cost = std::min(Cost, getCost(V) / getNumUsers(V) + C_Splat);
  }

  auto OPI = Pkr->getProducerInfo(VPCtx, OP);
  for (auto *VP : OPI.getProducers())
    Cost = std::min(Cost, getCost(VP));

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
        Cost = std::min(Cost, getCost(VP) / getNumUsers(VP) + C_Perm);
      } else {
        BitVector Intersection = OPI.Elements;
        Intersection &= VP->getElements();
        Cost = std::min(Cost, getCost(VP) / float(Intersection.count()) *
                                      float(OPI.Elements.count()) /
                                      getNumUsers(VP) +
                                  C_Shuffle);
      }
    }
  }

  return OrderedCosts[OP] = Cost;
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
      Cost = std::min(Cost, getCost(VP)/getNumUsers(VP) + C_Extract);
    }
  }
#endif

  return ScalarCosts[I] = Cost;
}

// FIXME: need to estimate cost of stores, which are not explicitly live-outs
float Heuristic::getCost(const Frontier *Frt) {
  NamedRegionTimer Timer("heuristic", "heuristic", "pack selection", "", false);
  float Cost = 0;
  for (const OperandPack *OP : Frt->getUnresolvedPacks())
    Cost += getCost(OP);
  for (Value *V : Frt->getUnresolvedScalars()) {
    Cost += getCost(V);
  }
  for (Value *V : VPCtx->iter_values(Frt->getFreeInsts())) {
    if (auto *SI = dyn_cast<StoreInst>(V))
      Cost += getCost(SI);
  }
  return Cost;
}
