#include "ControlDependence.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/Instructions.h"

using namespace llvm;

ControlDependenceAnalysis::ControlDependenceAnalysis(LoopInfo &LI,
                                                     DominatorTree &DT,
                                                     PostDominatorTree &PDT)
    : LI(LI), DT(DT), PDT(PDT) {
  // Run a half-ass GVN over the control conditions
  Function *F = DT.getRootNode()->getBlock()->getParent();
  ReversePostOrderTraversal<Function *> RPO(F);
  for (auto *BB : RPO) {
    auto *Br = dyn_cast_or_null<BranchInst>(BB->getTerminator());
    if (Br && Br->isConditional())
      (void)getCanonicalValue(Br->getCondition());
  }
}

Value *ControlDependenceAnalysis::getCanonicalValue(Value *V) {
  return V;
  if (auto *V2 = CanonicalValues.lookup(V))
    return V2;

  unsigned Opcode, Extra;
  Value *A, *B;
  if (auto *BO = dyn_cast<BinaryOperator>(V)) {
    Opcode = BO->getOpcode();
    Extra = 0;
    A = BO->getOperand(0);
    B = BO->getOperand(1);
  } else if (auto *Cmp = dyn_cast<CmpInst>(V)) {
    Opcode = Cmp->getOpcode();
    Extra = Cmp->getPredicate();
    A = Cmp->getOperand(0);
    B = Cmp->getOperand(1);
  } else {
    return V;
  }

  BinaryInstruction Inst{Opcode, Extra, getCanonicalValue(A),
                         getCanonicalValue(B)};
  if (auto *V2 = CanonicalInsts.lookup(Inst))
    return CanonicalValues[V] = V2;
  CanonicalInsts[Inst] = V;
  CanonicalValues[V] = V;
  return V;
}

static unsigned maxDepth(ArrayRef<const ControlCondition *> Conds) {
  if (Conds.empty())
    return 0;
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
  Cond = getCanonicalValue(Cond);
  AndKeyT Key(Parent, Cond);
  auto &Slot = IsTrue ? UniqueAndOfTrue[Key] : UniqueAndOfFalse[Key];
  if (!Slot) {
    Slot.reset(new ConditionAnd(Parent, Cond, IsTrue));
    Slot->Complement = getAnd(Parent, Cond, !IsTrue);
  }
  return Slot.get();
}

const ControlCondition *
ControlDependenceAnalysis::getOr(ArrayRef<const ControlCondition *> Conds) {
  if (Conds.empty())
    return nullptr;

  if (Conds.size() == 1)
    return Conds.front();

  decltype(UniqueOrs)::iterator It;
  bool Inserted;
  std::tie(It, Inserted) = UniqueOrs.try_emplace(OrKeyT(Conds), nullptr);
  if (Inserted) {
    It->second.reset(new ConditionOr(Conds));
    It->first = It->second->Conds;
  }
  return It->second.get();
}

const GammaNode *ControlDependenceAnalysis::getGamma(PHINode *PN) {
  decltype(Gammas)::iterator It;
  bool Inserted;
  std::tie(It, Inserted) = Gammas.try_emplace(PN);
  if (!Inserted)
    return It->second.get();

  auto *G = new GammaNode;
  G->PN = PN;
  It->second.reset(G);
  Value *V;
  BasicBlock *BB;
  for (auto Pair : zip(PN->incoming_values(), PN->blocks())) {
    std::tie(V, BB) = Pair;
    G->Vals.push_back(V);
    G->Conds.push_back(getConditionForEdge(BB, PN->getParent()));
  }
  return G;
}

const ControlCondition *
ControlDependenceAnalysis::getConditionForEdge(BasicBlock *Src,
                                               BasicBlock *Dst) {
  auto *SrcCond = getConditionForBlock(Src);
  auto *Br = cast<BranchInst>(Src->getTerminator());

  // Special case for exit edges
  auto *DstL = LI.getLoopFor(Dst);
  for (auto *SrcL = LI.getLoopFor(Src); SrcL && SrcL != DstL; SrcL = SrcL->getParentLoop()) {
    auto *PreheaderC = getConditionForBlock(SrcL->getLoopPreheader());
    SrcCond = concat(PreheaderC, SrcCond);
  }

  // Ignore backedges
  auto *L = LI.getLoopFor(Src);
  if (Br->isUnconditional() || (L && L->isLoopLatch(Src))) {
    return SrcCond;
  }
  return getAnd(SrcCond, Br->getCondition(), Br->getSuccessor(0) == Dst);
}

const ControlCondition *
ControlDependenceAnalysis::concat(const ControlCondition *CondA,
                                  const ControlCondition *CondB) {
  if (!CondA)
    return CondB;
  if (!CondB)
    return CondA;

  if (auto *And = dyn_cast<ConditionAnd>(CondB))
    return getAnd(concat(CondA, And->Parent), And->Cond, And->IsTrue);

  auto *Or = cast<ConditionOr>(CondB);
  SmallVector<const ControlCondition *> Conds;
  for (auto *C : Or->Conds)
    Conds.push_back(concat(CondA, C));
  return getOr(Conds);
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

  if (auto *L = LI.getLoopFor(BB)) {
    // We track the control condition of the main loop body separately
    auto *Header = L->getHeader();
    if (DT.dominates(Header, BB) && PDT.dominates(BB, Header))
      return nullptr;
  }

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
    if (And->Cond->hasName())
      OS << And->Cond->getName();
    else
      OS << *And->Cond;
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
  OS << "(" << &C << ")";
  return OS;
}

static int compareConditionsImpl(const ControlCondition *C1, const ControlCondition *C2);

static int compareAnd(const ConditionAnd *A1, const ConditionAnd *A2) {
  if (A1 == A2)
    return 0;
  if (A1->IsTrue != A2->IsTrue)
    return A1->IsTrue ? -1 : 1;
  int ParentCmp = compareConditionsImpl(A1->Parent, A2->Parent);
  if (ParentCmp != 0)
    return ParentCmp;
  return A1->Cond < A2->Cond ? -1 : 1;
}

static int compareOr(const ConditionOr *O1, const ConditionOr *O2) {
  if (O1 == O2)
    return 0;

  if (O1->Conds.size() != O2->Conds.size())
    return O1->Conds.size() < O2->Conds.size() ? -1 : 1;

  for (auto Pair : zip(O1->Conds, O2->Conds)) {
    int Cmp = compareConditionsImpl(std::get<0>(Pair), std::get<1>(Pair));
    if (Cmp != 0)
      return Cmp;
  }
  return 0;
}

static int compareConditionsImpl(const ControlCondition *C1, const ControlCondition *C2) {
  if (C1 == C2)
    return 0;

  if (!C1)
    return -1;

  if (!C2)
    return 1;

  auto *A1 = dyn_cast<ConditionAnd>(C1);
  auto *A2 = dyn_cast<ConditionAnd>(C2);
  auto *O1 = dyn_cast<ConditionOr>(C1);
  auto *O2 = dyn_cast<ConditionOr>(C2);
  if (A1 && A2)
    return compareAnd(A1, A2) > 0;
  if (O1 && O2)
    return compareOr(O1, O2) > 0;
  return (bool)A1;
}

bool compareConditions(const ControlCondition *C1, const ControlCondition *C2) {
  return compareConditionsImpl(C1, C2) <= 0;
}
