#include "ControlDependence.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/Instructions.h"

using namespace llvm;

const ControlCondition *
ControlDependenceAnalysis::getAnd(const ControlCondition *Parent, Value *Cond,
                                  bool IsTrue) {
  AndKeyT Key(Parent, Cond);
  std::unique_ptr<ControlCondition> &Slot =
      IsTrue ? UniqueAndOfTrue[Key] : UniqueAndOfFalse[Key];
  if (!Slot)
    Slot.reset(new ConditionAnd(Parent, Cond, IsTrue));
  return Slot.get();
}

const ControlCondition *
ControlDependenceAnalysis::getOr(const ControlCondition *A,
                                 const ControlCondition *B) {
  OrKeyT Key(A, B);
  std::unique_ptr<ControlCondition> &Slot = UniqueOrs[Key];
  if (!Slot)
    Slot.reset(new ConditionOr(A, B));
  return Slot.get();
}

// TODO: sort the conditions?
const ControlCondition *
ControlDependenceAnalysis::getOr(ArrayRef<const ControlCondition *> Conds) {
  auto *Or = Conds.front();
  for (auto *Cond : drop_begin(Conds))
    Or = getOr(Or, Cond);
  return Or;
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
  dump(OS, Or->A);
  OS << " \\/ ";
  dump(OS, Or->B);
  OS << ')';
}

raw_ostream &operator<<(raw_ostream &OS, const ControlCondition &C) {
  dump(OS, &C);
  return OS;
}
