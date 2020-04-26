#include "Solver.h"
#include "MatchManager.h"

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

class PackEnumerator {
  const std::vector<bool> &FreeInsts;
  const VectorPackContext &VPCtx;
  const LocalDependenceAnalysis &LDA;
  TargetTransformInfo *TTI;

  void
  enumeratePacksRec(const InstBinding *Inst,
                    const std::vector<ArrayRef<Operation::Match>> &LaneMatches,
                    std::vector<VectorPack *> &Enumerated, BitVector &Elements,
                    BitVector &Depended,
                    std::vector<const Operation::Match *> &Lanes) const {
    // The lane we are enumerating
    const unsigned LaneId = Lanes.size();

    auto BackupElements = Elements;
    auto BackupDepended = Depended;

    // Try out all matched operation for this line
    Lanes.push_back(nullptr);
    for (auto &Match : LaneMatches[LaneId]) {
      unsigned OutId = VPCtx.getScalarId(Match.Output);
      // Make sure we are allowed to use the matched instruction
      if (!FreeInsts[OutId])
        continue;
      // Make sure adding this `Match` doesn't violate any dependence constraint
      bool Independent = checkIndependence(
          LDA, VPCtx, cast<Instruction>(Match.Output), Elements, Depended);
      if (!Independent)
        continue;

      // Select this match.
      Elements.set(OutId);
      Depended |= LDA.getDepended(cast<Instruction>(Match.Output));
      Lanes.back() = &Match;

      if (LaneId < LaneMatches.size() - 1) {
        // Recursivly fill out the next lane
        enumeratePacksRec(Inst, LaneMatches, Enumerated, Elements, Depended,
                          Lanes);
      } else {
        // We are at the last lane.
        Enumerated.push_back(
            VPCtx.createVectorPack(Lanes, Elements, Depended, Inst, TTI));
      }

      // Revert the change before we try out the next match
      Elements = BackupElements;
      Depended = BackupDepended;
    }
    Lanes.pop_back();
  }

public:
  PackEnumerator(const std::vector<bool> &FreeInsts,
                 const VectorPackContext &VPCtx,
                 const LocalDependenceAnalysis &LDA, TargetTransformInfo *TTI)
      : FreeInsts(FreeInsts), VPCtx(VPCtx), LDA(LDA), TTI(TTI) {}
  void
  enumeratePacks(const InstBinding *Inst,
                 const std::vector<ArrayRef<Operation::Match>> &LaneMatches,
                 std::vector<VectorPack *> &Enumerated) const {
    std::vector<const Operation::Match *> EmptyPrefix;
    BitVector Elements(VPCtx.getNumValues());
    BitVector Depended(VPCtx.getNumValues());
    enumeratePacksRec(Inst, LaneMatches, Enumerated, Elements, Depended,
                      EmptyPrefix);
  }
};

std::vector<const VectorPack *>
Frontier::nextAvailablePacks(Packer *Packer) const {
  Instruction *I = getNextFreeInst();
  ArrayRef<InstBinding *> Insts = Packer->getInsts();
  auto &MM = Packer->getMatchManager(BB);
  auto &LDA = Packer->getLDA(BB);
  auto &LoadDAG = Packer->getLoadDAG(BB);
  auto &StoreDAG = Packer->getStoreDAG(BB);
  auto *TTI = Packer->getTTI();

  if (auto *LI = dyn_cast<LoadInst>(I)) {
  }

  if (auto *SI = dyn_cast<StoreInst>(I)) {
  }

  std::vector<VectorPack *> AvailablePacks;
  auto EnumeratePacks =
      [&](const InstBinding *Inst,
          const std::vector<ArrayRef<Operation::Match>> &LaneMatches) {
        assert(Inst->getLaneOps().size() == LaneMatches.size());
        unsigned N = 1;
        for (auto &Matches : LaneMatches)
          N *= Matches.size();

        BitVector Elements(VPCtx->getNumValues());
        BitVector Depended(VPCtx->getNumValues());
        for (unsigned i = 0; i < N; i++) {
          // `i` represent a particular member of the cross product.
          // Decode `i` here.
          unsigned Encoded = i;
          std::vector<const Operation::Match *> Lanes;
          for (auto &Matches : LaneMatches) {
            unsigned M = Matches.size();
            auto &Match = Matches[Encoded % M];

            // Make sure adding Match doesn't violate any dependence constraint
            bool Independent =
                checkIndependence(LDA, *VPCtx, cast<Instruction>(Match.Output),
                                  Elements, Depended);
            if (!Independent)
              break;

            Lanes.push_back(&Match);
            Encoded /= M;
          }

          if (Lanes.size() != Inst->getLaneOps().size())
            continue;

          AvailablePacks.push_back(
              VPCtx->createVectorPack(Lanes, Elements, Depended, Inst, TTI));
        }
      };

  PackEnumerator PackEnum(FreeInsts, *VPCtx, LDA, TTI);

  for (auto *Inst : Insts) {
    ArrayRef<BoundOperation> LaneOps = Inst->getLaneOps();
    unsigned NumLanes = LaneOps.size();
    // Iterate over all combination of packs, fixing `I` at the `i`'th lane
    for (unsigned i = 0; i < NumLanes; i++) {
      std::vector<ArrayRef<Operation::Match>> LaneMatches;
      for (unsigned LaneId = 0; LaneId < NumLanes; LaneId++) {
        ArrayRef<Operation::Match> Matches;
        if (LaneId == i)
          Matches = MM.getMatchesForOutput(LaneOps[i].getOperation(), I);
        else
          Matches = MM.getMatches(LaneOps[i].getOperation());

        // if we can't find matches for any given lanes, then we can't use
        // `Inst`
        if (Matches.empty())
          break;
        LaneMatches.push_back(Matches);
      }
      PackEnum.enumeratePacks(Inst, LaneMatches, AvailablePacks);
    }
  }
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
void UCTNode::expand(UCTNodeFactory *Factory, Packer *Packer,
                     llvm::TargetTransformInfo *TTI) {
  assert(OutEdges.empty() && "expanded already");
  float Cost;

  // Consider keeping the next free inst scalar
  auto *Next =
      Factory->getNode(Frt->advance(Frt->getNextFreeInst(), Cost, TTI));
  OutEdges.push_back(OutEdge{nullptr, Next, Cost});

  for (auto *VP : Frt->nextAvailablePacks(Packer)) {
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
      // If we haven't visited the dest of A, then give it infinite weight
      if (A.Next->visitCount() == 0)
        return false;
      // If we haven't visited the dest of B ...
      if (B.Next->visitCount() == 0)
        return true;

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
    CurNode->expand(Factory, Packer, TTI);
  }

  // ========= 4) Backpropagation ===========
  CurNode->update(LeafCost);
  float TotalCost = LeafCost;
  for (int i = Path.size() - 2; i >= 0; i--) {
    auto *Edge = Path[i];
    TotalCost += Path[i + 1]->Cost;
    Edge->Next->update(TotalCost);
  }
}
