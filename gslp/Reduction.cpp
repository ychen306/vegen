#include "Reduction.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/PatternMatch.h"

using namespace llvm;

// Suppose we are doing A + B, find A and B
static bool matchReduction(Value *Rdx, Value *&A, Value *&B, RecurKind Kind) {
  using namespace PatternMatch;
  switch (Kind) {
  case RecurKind::Add:
    return match(Rdx, m_Add(m_Value(A), m_Value(B)));
  case RecurKind::Mul:
    return match(Rdx, m_Mul(m_Value(A), m_Value(B)));
  case RecurKind::And:
    return match(Rdx, m_And(m_Value(A), m_Value(B)));
  case RecurKind::Or:
    return match(Rdx, m_Or(m_Value(A), m_Value(B)));
  case RecurKind::Xor:
    return match(Rdx, m_Xor(m_Value(A), m_Value(B)));
  case RecurKind::FAdd:
    return match(Rdx, m_FAdd(m_Value(A), m_Value(B)));
  case RecurKind::FMul:
    return match(Rdx, m_FMul(m_Value(A), m_Value(B)));
  case RecurKind::FMax:
    return match(Rdx, m_OrdFMax(m_Value(A), m_Value(B))) ||
           match(Rdx, m_UnordFMax(m_Value(A), m_Value(B)));
  case RecurKind::FMin:
    return match(Rdx, m_OrdFMin(m_Value(A), m_Value(B))) ||
           match(Rdx, m_UnordFMin(m_Value(A), m_Value(B)));
  case RecurKind::SMax:
    return match(Rdx, m_SMax(m_Value(A), m_Value(B)));
  case RecurKind::SMin:
    return match(Rdx, m_SMin(m_Value(A), m_Value(B)));
  case RecurKind::UMax:
    return match(Rdx, m_UMax(m_Value(A), m_Value(B)));
  case RecurKind::UMin:
    return match(Rdx, m_UMin(m_Value(A), m_Value(B)));
  default:
    return false;
  }
}

static bool cmpHasMoreThanOneUse(Value *V) {
  auto *Select = dyn_cast<SelectInst>(V);
  return Select && !Select->getCondition()->hasOneUse();
}

static void matchReductionTreeWithKind(Value *Root,
                                       SmallVectorImpl<Instruction *> &Ops,
                                       SmallVectorImpl<Value *> &Leaves,
                                       RecurKind Kind) {
  unsigned MaxNumUses =
      RecurrenceDescriptor::isMinMaxRecurrenceKind(Kind) ? 2 : 1;

  SmallVector<std::pair<Value *, unsigned>> Worklist{std::make_pair(Root, 0)},
      LeavesAndHeights;
  while (!Worklist.empty()) {
    auto ValAndHeight = Worklist.pop_back_val();
    Value *V = ValAndHeight.first;
    unsigned Height = ValAndHeight.second;
    Value *A, *B;
    // Only the root is allowed to have more than one use
    if ((V != Root && V->getNumUses() > MaxNumUses) ||
        cmpHasMoreThanOneUse(V) ||
        !matchReduction(V, A, B, Kind)) {
      LeavesAndHeights.emplace_back(V, Height);
      continue;
    }
    Ops.push_back(cast<Instruction>(V));
    Worklist.emplace_back(B, Height + 1);
    Worklist.emplace_back(A, Height + 1);
  }
  stable_sort(LeavesAndHeights,
              [](auto &P1, auto &P2) { return P1.second > P2.second; });
  for (auto &Pair : LeavesAndHeights)
    Leaves.push_back(Pair.first);
}

static RecurKind RdxKinds[] = {RecurKind::Add,  RecurKind::Mul,  RecurKind::And,
  RecurKind::Or,   RecurKind::Xor,  RecurKind::FAdd,
  RecurKind::FMul, RecurKind::FMin, RecurKind::FMax,
  RecurKind::SMin, RecurKind::SMax, RecurKind::UMin,
  RecurKind::UMax};

static bool matchReductionTree(PHINode *PN, Loop *L,
                               SmallVectorImpl<Instruction *> &Ops,
                               SmallVectorImpl<Value *> &Leaves,
                               RecurKind &Kind) {
  Value *Root = PN->getIncomingValueForBlock(L->getLoopLatch());
  for (RecurKind K : RdxKinds) {
    Ops.clear();
    Leaves.clear();
    matchReductionTreeWithKind(Root, Ops, Leaves, K);
    auto It = find(Leaves, PN);
    if (It != Leaves.end()) {
      Leaves.erase(It);
      Kind = K;
      return true;
    }
  }
  return false;
}

Optional<ReductionInfo> matchLoopReduction(PHINode *PN, LoopInfo &LI) {
  if (PN->getType()->isVectorTy())
    return None;

  auto *BB = PN->getParent();
  auto *L = LI.getLoopFor(BB);
  if (!L || !L->getLoopPreheader() || L->getHeader() != BB)
    return None;

  ReductionInfo RI;
  if (!matchReductionTree(PN, L, RI.Ops, RI.Elts, RI.Kind))
    return None;
  RI.Phi = PN;
  RI.StartValue = RI.Phi->getIncomingValueForBlock(L->getLoopPreheader());

  unsigned MaxNumUses =
      RecurrenceDescriptor::isMinMaxRecurrenceKind(RI.Kind) ? 2 : 1;
  // Don't vectorize phis that have more than one use
  if (PN->getNumUses() > MaxNumUses)
    return None;

  auto *Root = RI.Ops.front();
  // Don't vectorize if the reduced value have more than one *in-loop* use
  for (User *U : Root->users()) {
    if (U == PN)
      continue;
    if (L->contains(cast<Instruction>(U)->getParent()))
      return None;
  }

  return RI;
}

Optional<ReductionInfo> matchLoopFreeReduction(Value *Root) {
  ReductionInfo RI;
  RI.Phi = nullptr;
  auto &Leaves = RI.Elts;
  auto &Ops = RI.Ops;
  for (auto K : RdxKinds) {
    RI.Kind = K;
    Leaves.clear();
    Ops.clear();
    matchReductionTreeWithKind(Root, Ops, Leaves, K);
    if (Leaves.size() >= 4)
      return RI;
  }
  return None;
}

raw_ostream &operator<<(raw_ostream &OS, const ReductionInfo &RI) {
  OS << "reduction {";
  if (RI.Phi)
    OS << "\n\tphi = " << *RI.Phi;
  OS << "\n\troot = " << *RI.Ops.front();
  OS << "\n\telements = [";
  for (auto *V : RI.Elts) {
    OS << "\n\t\t" << *V;
  }
  OS << "\n\t]\n";
  OS << "}";
  return OS;
}
