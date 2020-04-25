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

template <typename T>
void removeAndSort(std::vector<T> &X, ArrayRef<unsigned> ToRemove) {
  for (unsigned i : ToRemove) {
    std::swap(X[i], X.back());
    X.pop_back();
  }
  std::sort(X.begin(), X.end());
}

} // namespace

void Frontier::freezeOneInst(unsigned InstId) {
  FreeInsts[InstId] = false;
  UnresolvedScalars[InstId] = false;
}

void Frontier::advanceBBIt() {
  if (auto *NextFreeInst = getNextFreeInst())
    BBIt = BasicBlock::reverse_iterator(NextFreeInst);
  else
    BBIt = BB->rend();
}

Frontier Frontier::advance(Instruction *I, float &Cost,
                           TargetTransformInfo *TTI) const {
  Frontier Next = *this;

  Next.freezeOneInst(VPCtx->getScalarId(I));
  Next.advanceBBIt();

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
      Cost +=
          TTI->getVectorInstrCost(Instruction::InsertElement, VecTy, LaneId);
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
bool Frontier::resolveOperandPack(const VectorPack &VP,
                                  UnresolvedOperandPack &UP) {
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
static unsigned getGatherCost(const VectorPack &VP,
                              const VectorPack::OperandPack &OpndPack,
                              TargetTransformInfo *TTI) {
  return 2;
}

// FIXME: this doesn't work when there are lanes in VP that cover multiple
// instructions.
Frontier Frontier::advance(const VectorPack *VP, float &Cost,
                           TargetTransformInfo *TTI) const {
  Frontier Next = *this;

  Cost = VP->getCost();

  auto *VecTy = getVectorType(*VP);

  auto OutputLanes = VP->getOrderedValues();
  for (unsigned LaneId = 0; LaneId < OutputLanes.size(); LaneId++) {
    auto *I = cast<Instruction>(OutputLanes[LaneId]);
    unsigned InstId = VPCtx->getScalarId(I);

    // Pay the extract cost
    if (Next.UnresolvedScalars[InstId])
      Cost +=
          TTI->getVectorInstrCost(Instruction::ExtractElement, VecTy, LaneId);

    Next.freezeOneInst(InstId);
  }
  Next.advanceBBIt();

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
        Cost += TTI->getVectorInstrCost(Instruction::ExtractElement, OperandTy,
                                        LaneId);
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

// If we already have a UCTNode for the same frontier, reuse that node.
UCTNode *UCTNodeFactory::getNode(Frontier &&Frt) {
  decltype(Nodes)::iterator It;
  bool Inserted;
  std::tie(It, Inserted) = Nodes.emplace(Frt, UCTNode(nullptr));
  if (Inserted) {
    It->second.Frt = &It->first;
  }
  return &It->second;
}

// Fill out the children node
void UCTNode::expand(UCTNodeFactory *Factory, ArrayRef<InstBinding *> Insts,
                     llvm::TargetTransformInfo *TTI) {
  assert(OutEdges.empty() && "expanded already");
  float Cost;

  // Consider keeping the next free inst scalar
  auto *Next =
      Factory->getNode(Frt->advance(Frt->getNextFreeInst(), Cost, TTI));
  OutEdges.push_back(OutEdge{nullptr, Next, Cost});

  for (auto *VP : Frt->nextAvailablePacks(Insts)) {
    auto *Next = Factory->getNode(Frt->advance(VP, Cost, TTI));
    OutEdges.push_back(OutEdge{VP, Next, Cost});
  }
}

// Do one iteration of MCTS
void UCTSearch::refineSearchTree(UCTNode *Root) {
  // ========= 1) Selection ==========
  UCTNode *CurNode = Root;
  std::vector<const UCTNode::OutEdge *> Path;
  // Traverse down to a leaf node.
  while (CurNode->expanded()) {
    // Compare out-going edges by UCT score
    unsigned VisitCount = CurNode->visitCount();
    auto compareEdge = [VisitCount, this](const UCTNode::OutEdge &A,
                           const UCTNode::OutEdge &B) {
      return -A.Cost + A.Next->score(VisitCount, C) <
             -B.Cost + B.Next->score(VisitCount, C);
    };

    auto OutEdges = CurNode->next();

    // Select the node maximizing the UCT formula
    auto It = std::max_element(OutEdges.begin(), OutEdges.end(), compareEdge);
    Path.push_back(&*It);
    CurNode = It->Next;
  }

  float LeafCost = 0;
  // ========= 2) Expansion ==========
  if (!CurNode->isTerminal()) {
    // ======= 3) Evaluation/Simulation =======
    LeafCost = evalLeafNode(CurNode);
    CurNode->expand(Factory, InstPool, TTI);
  }

  // ========= 4) Backpropagation ===========
  CurNode->update(LeafCost);
  float TotalCost = LeafCost;
  for (int i = Path.size()-2; i >= 0; i--) {
    auto *Edge = Path[i];
    TotalCost += Path[i+1]->Cost;
    Edge->Next->update(TotalCost);
  }
}
