#include "Reduction.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/PatternMatch.h"

using namespace llvm;

// Suppose we are doing A + B, given A, find B
static Value *matchReductionValue(Instruction *Rdx, Value *A, RecurKind Kind) {
  using namespace PatternMatch;
  Value *B = nullptr;
  switch (Kind) {
  case RecurKind::Add:
    match(Rdx, m_c_Add(m_Specific(A), m_Value(B)));
    break;
  case RecurKind::Mul:
    match(Rdx, m_c_Mul(m_Specific(A), m_Value(B)));
    break;
  case RecurKind::And:
    match(Rdx, m_c_And(m_Specific(A), m_Value(B)));
    break;
  case RecurKind::Or:
    match(Rdx, m_c_Or(m_Specific(A), m_Value(B)));
    break;
  case RecurKind::Xor:
    match(Rdx, m_c_Xor(m_Specific(A), m_Value(B)));
    break;
  case RecurKind::FAdd:
    match(Rdx, m_c_FAdd(m_Specific(A), m_Value(B)));
    break;
  case RecurKind::FMul:
    match(Rdx, m_c_FMul(m_Specific(A), m_Value(B)));
    break;
  default:;
  }
  assert(B);
  return B;
}

Optional<RecurKind> matchLoopReduction(PHINode *PN, LoopInfo &LI,
                                      SmallVectorImpl<Value *> &Elts) {
  auto *L = LI.getLoopFor(PN->getParent());
  if (!L)
    return None;

  RecurrenceDescriptor Rdx;
  if (!RecurrenceDescriptor::isReductionPHI(PN, L, Rdx))
    return None;

  auto Kind = Rdx.getRecurrenceKind();

  auto Chain = Rdx.getReductionOpChain(PN, L);

  // Don't vectorize phis that have more than one in-loop use
  for (User *U : PN->users()) {
    if (U == Chain.front())
      continue;
    if (L->contains(cast<Instruction>(U)->getParent()))
      return None;
  }

  Value *Prev = PN;
  for (auto *Cur : Chain) {
    auto *Elt = matchReductionValue(Cur, Prev, Kind);
    // Don't vectorize reduction on values with more than one use
    if (!Elt->hasOneUse())
      return None;
    Elts.push_back(Elt);
    Prev = Cur;
  }
  return Kind;
}
