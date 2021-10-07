#ifndef CONTROL_DEPENDENCE_H
#define CONTROL_DEPENDENCE_H

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/Support/Casting.h"
#include <map>

namespace llvm {
class Value;
class BasicBlock;
class PostDominatorTree;
class DominatorTree;
class raw_ostream;
} // namespace llvm

class ControlCondition {
public:
  enum ConditionKind { Kind_ConditionAnd, Kind_ConditionOr };

private:
  const ConditionKind Kind;

public:
  ControlCondition(ConditionKind K) : Kind(K) {}
  ConditionKind getKind() const { return Kind; }
};

struct ConditionAnd : public ControlCondition {
  const ControlCondition *Parent;
  llvm::Value *Cond;
  bool IsTrue;

  static bool classof(const ControlCondition *C) {
    return C->getKind() == Kind_ConditionAnd;
  }

private:
  friend class ControlDependenceAnalysis;
  ConditionAnd(const ControlCondition *Parent, llvm::Value *Cond, bool IsTrue)
      : ControlCondition(Kind_ConditionAnd), Parent(Parent), Cond(Cond),
        IsTrue(IsTrue) {}
};

struct ConditionOr : public ControlCondition {
  const ControlCondition *A;
  const ControlCondition *B;

  static bool classof(const ControlCondition *C) {
    return C->getKind() == Kind_ConditionOr;
  }

private:
  friend class ControlDependenceAnalysis;
  ConditionOr(const ControlCondition *A, const ControlCondition *B)
      : ControlCondition(Kind_ConditionOr), A(A), B(B) {}
};

class ControlDependenceAnalysis {
  llvm::DominatorTree &DT;
  llvm::PostDominatorTree &PDT;
  using OrKeyT = std::pair<const ControlCondition *, const ControlCondition *>;
  llvm::DenseMap<OrKeyT, std::unique_ptr<ControlCondition>> UniqueOrs;
  using AndKeyT = std::pair<const ControlCondition *, llvm::Value *>;
  llvm::DenseMap<AndKeyT, std::unique_ptr<ControlCondition>> UniqueAndOfTrue;
  llvm::DenseMap<AndKeyT, std::unique_ptr<ControlCondition>> UniqueAndOfFalse;

  llvm::DenseMap<llvm::BasicBlock *, const ControlCondition *> BlockConditions;
  // use std::map to avoid reallocation/iterator stability
  std::map<llvm::BasicBlock *, llvm::SmallPtrSet<llvm::BasicBlock *, 4>>
      ControlDependentBlocks;

  const ControlCondition *getAnd(const ControlCondition *, llvm::Value *, bool);
  const ControlCondition *getOr(const ControlCondition *,
                                const ControlCondition *);
  const ControlCondition *getOr(llvm::ArrayRef<const ControlCondition *>);
  const llvm::SmallPtrSetImpl<llvm::BasicBlock *> &
  getControlDependentBlocks(llvm::BasicBlock *);

public:
  ControlDependenceAnalysis(llvm::DominatorTree &DT,
                            llvm::PostDominatorTree &PDT)
      : DT(DT), PDT(PDT) {}
  const ControlCondition *getConditionForBlock(llvm::BasicBlock *);
  const ControlCondition *getConditionForEdge(llvm::BasicBlock *,
                                              llvm::BasicBlock *);
};

llvm::raw_ostream &operator<<(llvm::raw_ostream &, const ControlCondition &);

#endif // CONTROL_DEPENDENCE_H
