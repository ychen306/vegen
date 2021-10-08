#include "ControlDependence.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/Instructions.h"

using namespace llvm;

static unsigned maxDepth(ArrayRef<const ControlCondition *> Conds) {
  unsigned Depth = ControlCondition::getDepth(Conds.front());
  for (auto *C : drop_begin(Conds))
    Depth = std::max(Depth, ControlCondition::getDepth(C));
  return Depth;
}

ConditionOr::ConditionOr(ArrayRef<const ControlCondition *> TheConds)
    : ControlCondition(Kind_ConditionOr, maxDepth(TheConds) + 1),
      Conds(TheConds.begin(), TheConds.end()),
      GreatestCommonCond(getGreatestCommonCondition(TheConds)) {}

const ControlCondition *getCommonCondForOr(const ControlCondition *C) {
  if (auto *Or = dyn_cast_or_null<ConditionOr>(C))
    return Or->GreatestCommonCond;
  return C;
}

const ControlCondition *getGreatestCommonCondition(const ControlCondition *C1,
                                                   const ControlCondition *C2) {
  C1 = getCommonCondForOr(C1);
  C2 = getCommonCondForOr(C2);
  if (!C1 || !C2)
    return nullptr;

  while (C1 != C2) {
    if (C1->depth() < C2->depth())
      std::swap(C1, C2);
    C1 = getCommonCondForOr(cast<ConditionAnd>(C1)->Parent);
    if (!C1)
      return nullptr;
  }
  return C1;
}

const ControlCondition *
getGreatestCommonCondition(ArrayRef<const ControlCondition *> Conds) {
  auto *C = Conds.front();
  for (auto *C2 : drop_begin(Conds))
    C = getGreatestCommonCondition(C, C2);
  return C;
}

const ControlCondition *
ControlDependenceAnalysis::getAnd(const ControlCondition *Parent, Value *Cond,
                                  bool IsTrue) {
  AndKeyT Key(Parent, Cond);
  auto &Slot = IsTrue ? UniqueAndOfTrue[Key] : UniqueAndOfFalse[Key];
  if (!Slot)
    Slot.reset(new ConditionAnd(Parent, Cond, IsTrue));
  return Slot.get();
}

const ControlCondition *
ControlDependenceAnalysis::getOr(ArrayRef<const ControlCondition *> Conds) {
  decltype(UniqueOrs)::iterator It;
  bool Inserted;
  std::tie(It, Inserted) = UniqueOrs.try_emplace(OrKeyT(Conds), nullptr);
  if (Inserted) {
    It->second.reset(new ConditionOr(Conds));
    It->first = It->second->Conds;
  }
  return It->second.get();
}

const ControlCondition *
ControlDependenceAnalysis::getConditionForEdge(BasicBlock *Src,
                                               BasicBlock *Dst) {
  auto *SrcCond = getConditionForBlock(Src);
  auto *Br = cast<BranchInst>(Src->getTerminator());
  if (Br->isUnconditional())
    return SrcCond;
  return getAnd(SrcCond, Br->getCondition(), Br->getSuccessor(0) == Dst);
}

// This is the same as computing the post dominance frontier of BB
const SmallPtrSetImpl<BasicBlock *> &
ControlDependenceAnalysis::getControlDependentBlocks(BasicBlock *BB) {
  auto It = ControlDependentBlocks.find(BB);
  if (It != ControlDependentBlocks.end())
    return It->second;

  auto &Blocks = ControlDependentBlocks[BB];

  // DF_local
  for (auto *Pred : predecessors(BB))
    if (!PDT.dominates(BB, Pred))
      Blocks.insert(Pred);

  // DF_up
  for (auto *Child : PDT.getNode(BB)->children())
    for (auto *BB2 : getControlDependentBlocks(Child->getBlock()))
      if (!PDT.dominates(BB, BB2))
        Blocks.insert(BB2);

  return Blocks;
}

const ControlCondition *
ControlDependenceAnalysis::getConditionForBlock(BasicBlock *BB) {
  auto It = BlockConditions.find(BB);
  if (It != BlockConditions.end())
    return It->second;

  // The entry block always executes unconditionally
  auto *Node = DT.getNode(BB);
  if (Node == DT.getRootNode())
    return nullptr;

  // Fast path:
  // If BB post-dominates its idom, BB has the same control condition
  BasicBlock *IDom = Node->getIDom()->getBlock();
  if (PDT.dominates(BB, IDom))
    return BlockConditions[BB] = getConditionForBlock(IDom);

  SmallVector<const ControlCondition *> CondsToJoin;
  for (auto *BB2 : getControlDependentBlocks(BB)) {
    BasicBlock *DstBB = nullptr;
    auto *Br = cast<BranchInst>(BB2->getTerminator());
    assert(Br->isConditional());
    // find the edge taken from the ctrl dependent block
    if (PDT.dominates(BB, Br->getSuccessor(0)))
      DstBB = Br->getSuccessor(0);
    else if (PDT.dominates(BB, Br->getSuccessor(1)))
      DstBB = Br->getSuccessor(1);
    assert(DstBB);
    CondsToJoin.push_back(getConditionForEdge(BB2, DstBB));
  }
  sort(CondsToJoin);
  return BlockConditions[BB] = getOr(CondsToJoin);
}

static void dump(raw_ostream &OS, const ControlCondition *C) {
  if (!C) {
    OS << "true";
    return;
  }

  if (auto *And = dyn_cast<ConditionAnd>(C)) {
    OS << '(';
    if (And->Parent) {
      dump(OS, And->Parent);
      OS << " /\\ ";
    }
    if (!And->IsTrue)
      OS << "not ";
    OS << And->Cond->getName();
    OS << ')';
    return;
  }
  auto *Or = cast<ConditionOr>(C);
  OS << '(';
  dump(OS, Or->Conds.front());
  for (auto *C2 : drop_begin(Or->Conds)) {
    OS << " \\/ ";
    dump(OS, C2);
  }
  OS << ')';
}

raw_ostream &operator<<(raw_ostream &OS, const ControlCondition &C) {
  dump(OS, &C);
  return OS;
}
