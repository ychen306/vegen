#include "Heuristic.h"
#include "Packer.h"
#include "Solver.h"
#include "llvm/Support/Timer.h"

using namespace llvm;

static constexpr float C_Splat = 1.0;
static constexpr float C_Insert = 2;
static constexpr float C_Perm = 0.5;
static constexpr float C_Shuffle = 0.5;
static constexpr float C_Extract = 1.0;

float Heuristic::getCost(const VectorPack *VP) {
  float Cost = VP->getProducingCost();
  for (auto *OP : VP->getOperandPacks())
    Cost += getCost(OP);
  return Cost;
}

float Heuristic::getCost(const OperandPack *OP) {
  auto It = OrderedCosts.find(OP);
  if (It != OrderedCosts.end())
    return It->second;

  OrderedCosts[OP] = 0;

  // Build by explicit insertion
  float Cost = 0;
  SmallPtrSet<Value *, 8> Inserted;
  for (auto *V : *OP)
    if (V && !isa<Constant>(V) && Inserted.insert(V).second)
      Cost += getCost(V) + C_Insert;

  if (Cost == 0)
    return 0;

  // Build by broadcast
  if (is_splat(*OP))
    Cost = std::min(Cost, getCost(OP->front()) + C_Splat);

  const OperandPack *Deduped = VPCtx->dedup(OP);
  float ExtraCost = Deduped != OP ? C_Shuffle : 0;
  auto OPI = Pkr->getProducerInfo(VPCtx, Deduped);
  for (auto *VP : OPI.getProducers())
    Cost = std::min(Cost, getCost(VP) + ExtraCost);

  if (!Candidates)
    return OrderedCosts[OP] = Cost;

  DenseSet<const VectorPack *> Visited;
  for (unsigned InstId : OPI.Elements.set_bits()) {
    for (auto *VP : Candidates->Inst2Packs[InstId]) {
      if (!Visited.insert(VP).second)
        continue;
      ArrayRef<Value *> Vals = VP->getOrderedValues();
      // FIXME: consider don't care
      if (Vals.size() == OPI.Elements.count() &&
          std::is_permutation(Vals.begin(), Vals.end(), OP->begin())) {
        Cost = std::min(Cost, getCost(VP) + C_Perm + ExtraCost);
      } else {
        BitVector Intersection = OPI.Elements;
        Intersection &= VP->getElements();
        Cost = std::min(Cost, (getCost(VP) + C_Shuffle + ExtraCost) /
                                  float(Intersection.count()) *
                                  float(OPI.Elements.count()));
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

  float Cost = Pkr->getScalarCost(I);
  for (Value *V : I->operands())
    Cost += getCost(V);
  return ScalarCosts[I] = Cost;
}

// FIXME: need to estimate cost of stores, which are not explicitly live-outs
float Heuristic::getCost(const Frontier *Frt) {
  NamedRegionTimer Timer("heuristic", "heuristic", "pack selection", "", false);
  float Cost = 0;
  for (const OperandPack *OP : Frt->getUnresolvedPacks())
    Cost += getCost(OP);
  for (Value *V : Frt->getUnresolvedScalars())
    Cost += getCost(V);
  for (Value *V : VPCtx->iter_values(Frt->getFreeInsts()))
    if (auto *SI = dyn_cast<StoreInst>(V))
      Cost += getCost(SI);
  return Cost;
}
