#include "Heuristic.h"
#include "Packer.h"
#include "Solver.h"
#include "VectorPack.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/CommandLine.h"

using namespace llvm;

#define DEBUG_TYPE "heuristic"

static constexpr float C_Splat = 1.0;
static constexpr float C_Perm = 2;
static constexpr float C_Insert = 2;
static constexpr float C_Shuffle = 2;
static constexpr float C_Extract = 1.0;

static cl::opt<bool> AllowDeinterleave("allow-deinterleave", cl::init(false));
static cl::opt<bool> AllowTranspose("allow-transpose", cl::init(false));

float Heuristic::getCost(const VectorPack *VP) {
  float Cost = VP->getProducingCost();
  for (auto *OP : VP->getOperandPacks()) {
    // Hack, don't include the cost of comparison
    if (all_of(*OP, [](Value *V) { return isa_and_nonnull<CmpInst>(V); }))
      continue;
    Cost += getCost(OP);
  }
  return Cost;
}

SmallVector<const OperandPack *> deinterleave(const VectorPackContext *VPCtx,
                                              const OperandPack *OP,
                                              unsigned Stride);

// interpret OP as an N x M matrix and transpose it
const OperandPack *transpose(const VectorPackContext *VPCtx,
                             const OperandPack *OP, unsigned N) {
  if (OP->size() % N)
    return nullptr;
  unsigned M = OP->size() / N;
  OperandPack T;
  for (unsigned i = 0; i < M; i++)
    for (unsigned j = 0; j < N; j++)
      T.push_back((*OP)[j * M + i]);
  return VPCtx->getCanonicalOperandPack(T);
}

Heuristic::Solution Heuristic::solve(const OperandPack *OP) {
  auto It = Solutions.find(OP);
  if (It != Solutions.end())
    return It->second;

  Solutions[OP] = 0;

  // Build by explicit insertion
  float Cost = 0;
  SmallPtrSet<Value *, 8> Inserted;
  for (auto Item : enumerate(*OP)) {
    auto *V = Item.value();
    if (V && !isa<Constant>(V) && Inserted.insert(V).second)
      Cost += getCost(V) + C_Insert;
  }

  // The baseline solution is building the vector by implicit insertion
  Solution Sol(Cost);
  LLVM_DEBUG(dbgs() << "Scalar cost of " << *OP << " = " << Cost << '\n');

  if (Cost == 0) {
    Solutions[OP] = Sol;
    return Sol;
  }

  // Build by broadcast
  float BroadcastCost = getCost(OP->front()) + C_Splat;
  if (is_splat(*OP) && Cost > BroadcastCost) {
    return Solutions[OP] = Solution(BroadcastCost);
  }

  auto *VPCtx = Pkr->getContext();

  const OperandPack *Deduped = VPCtx->dedup(OP);
  float ExtraCost = Deduped != OP ? C_Shuffle : 0;
  auto OPI = Pkr->getProducerInfo(Deduped);
  for (auto *VP : OPI.getProducers()) {
    Sol.update(Solution(getCost(VP) + ExtraCost, VP));
    LLVM_DEBUG(dbgs() << "Cost of " << *VP << ": " << getCost(VP) << '\n');
  }

  if (AllowTranspose) {
    for (unsigned N : {2, 4, 8})
      if (auto *T = transpose(VPCtx, OP, N)) {
        auto OPI = Pkr->getProducerInfo(T);
        for (auto *VP : OPI.getProducers())
          Sol.update(Solution(getCost(VP) + C_Perm, VP));
      }
  }

  if (AllowDeinterleave) {
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
        if (Cost > Sol.Cost)
          break;
      }
      Sol.update(Solution(Cost, Packs));
    }
  }

#if 1
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
        Sol.update(
            Solution(getCost(VP) * Discount + C_Shuffle + ExtraCost, VP));
      }
    }
  }
#endif

  return Solutions[OP] = Sol;
}

float Heuristic::getCost(Value *V) {
  if (!V)
    return 0;
  auto *I = dyn_cast<Instruction>(V);
  if (!I)
    return 0;

  auto It = ScalarCosts.find(I);
  if (It != ScalarCosts.end())
    return It->second;

  // Hack to get around phi nodes, which introduce cycles.
  ScalarCosts[I] = 0;

  float Cost = Pkr->getScalarCost(I);
  for (Value *V : I->operands())
    Cost += getCost(V);
  return ScalarCosts[I] = Cost;
}
