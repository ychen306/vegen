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
  default:
    return false;
  }
}

static void matchReductionTreeWithKind(Value *Root,
                                       SmallVectorImpl<Instruction *> &Ops,
                                       SmallVectorImpl<Value *> &Leaves,
                                       RecurKind Kind) {
  SmallVector<Value *> Worklist{Root};
  while (!Worklist.empty()) {
    auto *V = Worklist.pop_back_val();
    Value *A, *B;
    // Only the root is allowed to have more than one use
    if ((V != Root && !V->hasOneUse()) || !matchReduction(V, A, B, Kind)) {
      Leaves.push_back(V);
      continue;
    }
    Ops.push_back(cast<Instruction>(V));
    Worklist.push_back(A);
    Worklist.push_back(B);
  }
}

static bool matchReductionTree(PHINode *PN, Loop *L,
                               SmallVectorImpl<Instruction *> &Ops,
                               SmallVectorImpl<Value *> &Leaves,
                               RecurKind &Kind) {
  auto Kinds = {RecurKind::Add, RecurKind::Mul,  RecurKind::And, RecurKind::Or,
                RecurKind::Xor, RecurKind::FAdd, RecurKind::FMul};
  Value *Root = PN->getIncomingValueForBlock(L->getLoopLatch());
  for (RecurKind K : Kinds) {
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
  auto *BB = PN->getParent();
  auto *L = LI.getLoopFor(BB);
  if (!L || L->getHeader() != BB)
    return None;

  ReductionInfo RI;
  if (!matchReductionTree(PN, L, RI.Ops, RI.Elts, RI.Kind))
    return None;
  RI.Phi = PN;
  RI.StartValue = RI.Phi->getIncomingValueForBlock(L->getLoopPreheader());

  // Don't vectorize phis that have more than one use
  if (!PN->hasOneUse())
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

raw_ostream &operator<<(raw_ostream &OS, const ReductionInfo &RI) {
  return OS << "reduction { "
    << "phi = " << *RI.Phi
    << ", root = " << *RI.Ops.front()
    << "}";
}
