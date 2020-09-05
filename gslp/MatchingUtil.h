#ifndef MATCHING_UTIL_H
#define MATCHING_UTIL_H
#include "llvm/IR/PatternMatch.h"
//#include <utility>

namespace llvm {
namespace PatternMatch {

template <typename LHS, typename RHS> struct Pred_match {
  CmpInst::Predicate Pred;
  LHS L;
  RHS R;

  Pred_match(CmpInst::Predicate Pred, const LHS &L, const RHS &R)
      : Pred(Pred), L(L), R(R) {}

  template <typename OpTy> bool match(OpTy *V) {
    auto *CI = dyn_cast<CmpInst>(V);
    return CI && CI->getPredicate() == Pred && L.match(CI->getOperand(0)) &&
           R.match(CI->getOperand(1));
  }
};

template <typename LHS, typename RHS>
inline Pred_match<LHS, RHS> m_CmpWithPred(CmpInst::Predicate Pred, const LHS &L,
                                          const RHS &R) {
  return Pred_match<LHS, RHS>(Pred, L, R);
}

// match the pattern `(a cmp b) ? l : r`
template <typename ATy, typename BTy, typename LTy, typename RTy>
struct SelectOnCmp_match {
  CmpInst::Predicate Pred;
  ATy A;
  BTy B;
  LTy L;
  RTy R;

  SelectOnCmp_match(CmpInst::Predicate Pred, const ATy &A, const BTy &B,
                    const LTy &L, const RTy &R)
      : Pred(Pred), A(A), B(B), L(L), R(R) {}

  template <typename OpTy> bool match(OpTy *V) {
    auto *SI = dyn_cast<SelectInst>(V);
    if (!SI)
      return false;
    auto *CI = dyn_cast<CmpInst>(SI->getCondition());
    if (!CI)
      return false;
    return (CI->getPredicate() == Pred && A.match(CI->getOperand(0)) &&
            B.match(CI->getOperand(1)) && L.match(SI->getTrueValue()) &&
            R.match(SI->getFalseValue())) ||
           (CI->getPredicate() == CmpInst::getSwappedPredicate(Pred) &&
            A.match(CI->getOperand(0)) && B.match(CI->getOperand(1)) &&
            L.match(SI->getFalseValue()) && R.match(SI->getTrueValue()));
  }
};

template <typename ATy, typename BTy, typename LTy, typename RTy>
inline SelectOnCmp_match<ATy, BTy, LTy, RTy>
m_SelectOnCmp(CmpInst::Predicate Pred, const ATy &A, const BTy &B, const LTy &L,
              const RTy &R) {
  return SelectOnCmp_match<ATy, BTy, LTy, RTy>(Pred, A, B, L, R);
}

template <typename PatTuple, size_t... Is>
bool match_patterns(PatTuple &Pats, ArrayRef<Value *> Values,
                    std::index_sequence<Is...>) {
  bool Matched = true;
  (void)std::initializer_list<int>{
      (Matched = Matched && std::get<Is>(Pats).match(Values[Is]), 0)...};
  return Matched;
}

static void collectReducedValues(Instruction::BinaryOps Op, Value *V,
                                 std::vector<Value *> &Leaves) {
  auto *I = dyn_cast<Instruction>(V);
  bool IsLeaf = !I || I->getOpcode() != Op;
  if (!IsLeaf) {
    collectReducedValues(Op, I->getOperand(0), Leaves);
    collectReducedValues(Op, I->getOperand(1), Leaves);
  } else {
    Leaves.push_back(V);
  }
}

template <typename... PatTys> struct Reduction_match {
  Instruction::BinaryOps Op;
  std::tuple<PatTys...> Pats;

  Reduction_match(Instruction::BinaryOps Op, const PatTys &... Pats)
      : Op(Op), Pats(Pats...) {}

  template <typename OpTy> bool match(OpTy *Root) {
    std::vector<Value *> Leaves;
    collectReducedValues(Op, Root, Leaves);

    return Leaves.size() != sizeof...(PatTys) &&
           match_patterns(Pats, Leaves, std::index_sequence_for<PatTys...>());
  }
};

template <typename... PatTys>
Reduction_match<PatTys...> m_Reduction(Instruction::BinaryOps Op,
                                       const PatTys &... Pats) {
  return Reduction_match<PatTys...>(Op, Pats...);
}

// specialization for a to allow SExt to match a constant
template <> template<typename OpTy>
bool CastClass_match<bind_ty<Value>, Instruction::SExt>::match(OpTy *V) {
  if (auto *CI = dyn_cast<ConstantInt>(V)) {
    auto X = CI->getValue();
    auto *TruncatedTy = IntegerType::get(V->getType()->getContext(), X.getBitWidth()/2);
    return Op.match(ConstantInt::get(TruncatedTy, X.trunc(X.getBitWidth()/2)));
  }

  if (auto *O = dyn_cast<SExtInst>(V))
    return Op.match(O->getOperand(0));
  return false;
}

} // end namespace PatternMatch
} // end namespace llvm

#endif // end MATCHING_UTIL_H
