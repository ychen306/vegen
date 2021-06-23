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

SmallVector<const OperandPack *> deinterleave(const VectorPackContext *VPCtx, const OperandPack *OP, unsigned Stride);

Heuristic::Solution Heuristic::solve(const OperandPack *OP) {
  auto It = Solutions.find(OP);
  if (It != Solutions.end())
    return It->second;

  // Build by explicit insertion
  float Cost = 0;
  SmallPtrSet<Value *, 8> Inserted;
  for (auto *V : *OP)
    if (V && !isa<Constant>(V) && Inserted.insert(V).second)
      Cost += getCost(V) + C_Insert;

  // The baseline solution is building the vector by implicit insertion
  Solution Sol(Cost);

  if (Cost == 0) {
    Solutions[OP] = Sol;
    return Sol;
  }

  // Build by broadcast
  float BroadcastCast = getCost(OP->front()) + C_Splat;
  if (is_splat(*OP) && Cost > BroadcastCast)
    Sol = Solution(BroadcastCast);

  const OperandPack *Deduped = VPCtx->dedup(OP);
  float ExtraCost = Deduped != OP ? C_Shuffle : 0;
  auto OPI = Pkr->getProducerInfo(VPCtx, Deduped);
  for (auto *VP : OPI.getProducers()) {
    Sol.update(Solution(getCost(VP) + ExtraCost, VP));
  }

  // try to deinterleave the vector and produce it that way
  for (unsigned Stride : {2, 4, 8}) {
    if (Deduped->size() % Stride)
      continue;
    SmallVector<const VectorPack *> Packs;
    auto OPs = deinterleave(VPCtx, Deduped, Stride);
    float Cost = C_Shuffle * OPs.size();
    for (auto OP2 : OPs) {
      auto Sol2 = solve(OP2);
      Packs.append(Sol2.Packs);
      Cost += Sol2.Cost;
    }
    Sol.update(Solution(Cost, Packs));
  }

  if (!Candidates)
    return Solutions[OP] = Sol;

  DenseSet<const VectorPack *> Visited;
  for (unsigned InstId : OPI.Elements.set_bits()) {
    for (auto *VP : Candidates->Inst2Packs[InstId]) {
      if (!Visited.insert(VP).second || !VP->isLoad())
        continue;
      ArrayRef<Value *> Vals = VP->getOrderedValues();
      // FIXME: consider don't care
      if (Vals.size() == OPI.Elements.count() &&
          std::is_permutation(Vals.begin(), Vals.end(), OP->begin())) {
        Sol.update(Solution(getCost(VP) + C_Perm + ExtraCost, VP));
      } else {
        BitVector Intersection = OPI.Elements;
        Intersection &= VP->getElements();
        float Discount =
            (float)OPI.Elements.count() / (float)Intersection.count();
        Sol.update(Solution(getCost(VP) * Discount + C_Shuffle + ExtraCost, VP));
      }
    }
  }

  return Solutions[OP] = Sol;
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
