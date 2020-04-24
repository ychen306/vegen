#include "Solver.h"

using namespace llvm;

Frontier::Frontier(BasicBlock *BB, const VectorPackContext *VPCtx)
  : BB(BB), VPCtx(VPCtx), BBIt(BB->rbegin()),
  UnresolvedScalars(VPCtx->getNumValues(), false),
  FreeInsts(VPCtx->getNumValues(), true) {
  // Find external uses of any instruction `I` in `BB`
  // and mark `I` as an unresolved scalar.
  for (auto &I : *BB) {
    for (User *U : I.users()) {
      auto UserInst = dyn_cast<Instruction>(U);
      if (UserInst && UserInst->getParent() != BB) {
        UnresolvedScalars[VPCtx->getScalarId(&I)] = true;
        break;
      }
    }
  }
}

Instruction *Frontier::getNextFreeInst() const {
  for (auto I = BBIt, E = BB->rend(); I != E; ++I)
    if (FreeInsts[VPCtx->getScalarId(&*I)])
      return &*I;
  return nullptr;
}

namespace {

template<typename T>
void removeAndSort(std::vector<T> &X, ArrayRef<unsigned> ToRemove) {
  for (unsigned i : ToRemove) {
    std::swap(X[i], X.back());
    X.pop_back();
  }
  std::sort(X.begin(), X.end());
}

}

void Frontier::freezeOneInst(unsigned InstId) {
  FreeInsts[InstId] = false;
  UnresolvedScalars[InstId] = false;
}

Frontier Frontier::advance(Instruction *I, float &Cost, TargetTransformInfo *TTI) const {
  Frontier Next = *this;

  Next.freezeOneInst(VPCtx->getScalarId(I));

  if (auto *NextFreeInst = Next.getNextFreeInst())
    Next.BBIt = BasicBlock::reverse_iterator(NextFreeInst);
  else
    Next.BBIt = BB->rend();

  // Go over unresolved packs and see if we've resolved any lanes
  Cost = 0;
  SmallVector<unsigned, 2> ResolvedPackIds;
  for (unsigned i = 0; i < Next.UnresolvedPacks.size(); i++) {
    auto &UP = Next.UnresolvedPacks[i];
    auto *VecTy = getVectorType(*UP.Pack);

    // Special case: we can build UP by broadcasting `I`.
    if (is_splat(*UP.Pack)) {
      Cost += TTI->getShuffleCost(TargetTransformInfo::SK_Broadcast, VecTy, 0);
      ResolvedPackIds.push_back(i);
      continue;
    }

    for (unsigned LaneId = 0; LaneId < UP.Pack->size(); LaneId++) {
      if ((*UP.Pack)[LaneId] != I)
        continue;
      // Pay the insert cost
      Cost += TTI->getVectorInstrCost(Instruction::InsertElement, VecTy, LaneId);
      UP.resolveOneLane(LaneId);
    }
    if (UP.resolved())
      ResolvedPackIds.push_back(i);
  }

  // If `I` uses any free instructions,
  // add those to the set of unresolved scalars.
  for (Value *Operand : I->operands()) {
    auto *I2 = dyn_cast<Instruction>(Operand);
    if (!I2 || I2->getParent() != BB)
      continue;
    unsigned InstId = VPCtx->getScalarId(I2);
    if (Next.FreeInsts[InstId])
      Next.UnresolvedScalars[InstId] = true;
  }

  removeAndSort(Next.UnresolvedPacks, ResolvedPackIds);

  return Next;
}

// Check whether there are lanes in `OpndPack` that are produced by `VP`.
// Also resolve those lanes if exist.
bool Frontier::resolveOperandPack(const VectorPack &VP, UnresolvedOperandPack &UP) {
  bool Produced = false;
  for (unsigned LaneId = 0; LaneId < UP.Pack->size(); LaneId++) {
    auto *V = (*UP.Pack)[LaneId];
    auto *I = dyn_cast<Instruction>(V);
    if (!I || I->getParent() != BB)
      continue;
    if (VP.getElements().test(VPCtx->getScalarId(I))) {
      UP.resolveOneLane(LaneId);
      Produced = true;
    }
  }
  return Produced;
}

// Return the cost of gathering from `VP` to `OpndPack`
static unsigned
getGatherCost(const VectorPack &VP, const VectorPack::OperandPack &OpndPack, TargetTransformInfo *TTI) {
  return 2;
}

// FIXME: this doesn't work when there are lanes in VP that cover multiple instructions.
Frontier Frontier::advance(const VectorPack *VP, float &Cost, TargetTransformInfo *TTI) const {
  Frontier Next = *this;

  Cost = VP->getCost();

  auto *VecTy = getVectorType(*VP);

  auto OutputLanes = VP->getOrderedValues();
  for (unsigned LaneId = 0; LaneId < OutputLanes.size(); LaneId++) {
    auto *I = cast<Instruction>(OutputLanes[LaneId]);
    unsigned InstId = VPCtx->getScalarId(I);

    // Pay the extract cost
    if (Next.UnresolvedScalars[InstId])
      Cost += TTI->getVectorInstrCost(Instruction::ExtractElement, VecTy, LaneId);

    Next.freezeOneInst(InstId);
  }

  SmallVector<unsigned, 2> ResolvedPackIds;
  for (unsigned i = 0; i < Next.UnresolvedPacks.size(); i++) {
    auto &UP = Next.UnresolvedPacks[i];
    if (bool PartiallyResolved = Next.resolveOperandPack(*VP, UP)) {
      Cost += getGatherCost(*VP, *UP.Pack, TTI);
      if (UP.resolved())
        ResolvedPackIds.push_back(i);
    }
  }

  // Track the unresolved operand packs used by `VP`
  for (auto &OpndPack : VP->getOperandPacks()) {
    UnresolvedOperandPack UP(OpndPack);
    auto *OperandTy = getVectorType(OpndPack);
    for (unsigned LaneId = 0; LaneId < OpndPack.size(); LaneId++) {
      auto *V = OpndPack[LaneId];
      if (isa<Constant>(V))
        continue;
      auto *I = dyn_cast<Instruction>(V);
      if (!I || I->getParent() != BB) {
        // Assume I is always scalar and pay the insert cost.
        Cost += TTI->getVectorInstrCost(Instruction::ExtractElement, OperandTy, LaneId);
        UP.resolveOneLane(LaneId);
      } else if (Next.isFreeInst(I))
        UP.resolveOneLane(LaneId);
    }

    if (!UP.resolved())
      Next.UnresolvedPacks.push_back(std::move(UP));
  }

  removeAndSort(Next.UnresolvedPacks, ResolvedPackIds);

  return Next;
}
