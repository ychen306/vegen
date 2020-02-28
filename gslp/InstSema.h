#ifndef INST_SEMA_H
#define INST_SEMA_H

#include "llvm/IR/Value.h"
#include "llvm/ADT/APInt.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/IR/IRBuilder.h"
#include <vector>

struct InstSignature {
  std::vector<unsigned> InputBitwidths;
  std::vector<unsigned> OutputBitwidths;
  bool HasImm8;
};

struct InputSlice {
  unsigned InputId;
  unsigned Lo, Hi;

  unsigned size() { return Hi - Lo; }

  bool operator<(InputSlice &Other) const {
    return std::tie(InputId, Lo, Hi)
      < std::tie(Other.InputId, Other.Lo, Other.Hi);
  }
};

// Interface that abstractly defines an operation
struct Operation {
  typedef std::vector<const llvm::Value *> Match;
  virtual bool numLiveins() const = 0;
  // `match' returns true if `V` is matched.
  // If a match is found, additionally return the matched liveins
  virtual bool match(const llvm::Value *V, std::vector<Match> &Matches) const = 0;
};

// An operation explicitly bound to an instruction and its input(s)
class BoundOperation {
  const Operation *Op;
  std::vector<InputSlice> BoundSlices;

public:
  // A bound operation
  BoundOperation(const Operation *Op, std::vector<InputSlice> BoundSlices)
      : Op(Op), BoundSlices(BoundSlices) {}
  const Operation *getOperation() const { return Op; }
};

// An instruction is a list of lanes,
// each of which characterized by a BoundOperation
class InstBinding {
  InstSignature Sig;
  std::vector<BoundOperation> LaneOps;
  std::string Name;
  
public:
  std::string getName() { return Name; }
  InstBinding(std::string Name, InstSignature Sig, std::vector<BoundOperation> LaneOps) 
    : Name(Name), Sig(Sig), LaneOps(LaneOps) {}
  llvm::ArrayRef<BoundOperation> getLaneOps() const { return LaneOps; }

  template <typename T, typename Inserter>
  llvm::Value *create(
      llvm::Module &InstWrappers,
      llvm::IRBuilder<T, Inserter> &Builder,
      llvm::ArrayRef<llvm::Value *> Operands,
      unsigned char Imm8=0) const;
};

// this one pulls all operation that we are interested in 
// and tries to match all of them while trying to avoid
// matching the same operation twice on the same value
class MatchManager {
  // record matches for each operation
  llvm::DenseMap<const Operation *, std::vector<Operation::Match>> Matches;

public:
  MatchManager(llvm::ArrayRef<InstBinding> Insts) {
    for (auto &Inst : Insts)
      for (auto &LaneOp : Inst.getLaneOps())
        Matches.FindAndConstruct(LaneOp.getOperation());
  }

  void match(const llvm::Value *V) {
    for (auto &KV : Matches) {
      const Operation *Op = KV.first;
      std::vector<Operation::Match> &Matches = KV.second;
      Op->match(V, Matches);
    }
  }

  llvm::ArrayRef<Operation::Match> getMatches(const Operation *Op) const {
    return Matches.lookup(Op);
  }
};

template <typename LHS_TY, typename RHS_TY>
llvm::PatternMatch::CmpClass_match<LHS_TY, RHS_TY, llvm::CmpInst, llvm::CmpInst::Predicate> 
m_Cmp_dont_care(llvm::CmpInst::Predicate Pred, LHS_TY LHS, RHS_TY RHS) {
  return llvm::PatternMatch::m_Cmp(Pred, LHS, RHS);
}

static bool hasBitWidth(const llvm::Value *V, unsigned BitWidth) {
  auto *Ty = V->getType();
  if (Ty->isIntegerTy())
    return Ty->getIntegerBitWidth() == BitWidth;
  if (Ty->isFloatTy())
    return BitWidth == 32;
  if (Ty->isDoubleTy())
    return BitWidth == 64;
  return false;
}

extern std::vector<InstBinding> Insts;

#endif // end INST_SEMA_H
