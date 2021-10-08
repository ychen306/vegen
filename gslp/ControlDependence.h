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
class LoopInfo;
class DominatorTree;
class raw_ostream;
} // namespace llvm

class ControlCondition {
public:
  enum ConditionKind { Kind_ConditionAnd, Kind_ConditionOr };

private:
  const ConditionKind Kind;
  const unsigned Depth;

public:
  ControlCondition(ConditionKind K, unsigned Depth) : Kind(K), Depth(Depth) {}
  ConditionKind getKind() const { return Kind; }
  unsigned depth() const { return Depth; }
  static unsigned getDepth(const ControlCondition *C) {
    return C ? C->depth() : 0;
  }
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
      : ControlCondition(Kind_ConditionAnd, getDepth(Parent) + 1),
        Parent(Parent), Cond(Cond), IsTrue(IsTrue) {}
};

struct ConditionOr : public ControlCondition {
  llvm::SmallVector<const ControlCondition *> Conds;
  const ControlCondition *GreatestCommonCond;

  static bool classof(const ControlCondition *C) {
    return C->getKind() == Kind_ConditionOr;
  }

private:
  friend class ControlDependenceAnalysis;
  ConditionOr(llvm::ArrayRef<const ControlCondition *> Conds);
};

class ControlDependenceAnalysis {
  llvm::LoopInfo &LI;
  llvm::DominatorTree &DT;
  llvm::PostDominatorTree &PDT;

  using OrKeyT = llvm::ArrayRef<const ControlCondition *>;
  llvm::DenseMap<OrKeyT, std::unique_ptr<ConditionOr>> UniqueOrs;
  using AndKeyT = std::pair<const ControlCondition *, llvm::Value *>;
  llvm::DenseMap<AndKeyT, std::unique_ptr<ConditionAnd>> UniqueAndOfTrue;
  llvm::DenseMap<AndKeyT, std::unique_ptr<ConditionAnd>> UniqueAndOfFalse;

  llvm::DenseMap<llvm::BasicBlock *, const ControlCondition *> BlockConditions;
  // use std::map to avoid reallocation/iterator stability
  std::map<llvm::BasicBlock *, llvm::SmallPtrSet<llvm::BasicBlock *, 4>>
      ControlDependentBlocks;

  const ControlCondition *getAnd(const ControlCondition *, llvm::Value *, bool);
  const ControlCondition *getOr(llvm::ArrayRef<const ControlCondition *>);
  const llvm::SmallPtrSetImpl<llvm::BasicBlock *> &
  getControlDependentBlocks(llvm::BasicBlock *);

public:
  ControlDependenceAnalysis(llvm::LoopInfo &LI, llvm::DominatorTree &DT,
                            llvm::PostDominatorTree &PDT)
      : LI(LI), DT(DT), PDT(PDT) {}
  const ControlCondition *getConditionForBlock(llvm::BasicBlock *);
  const ControlCondition *getConditionForEdge(llvm::BasicBlock *,
                                              llvm::BasicBlock *);
};

llvm::raw_ostream &operator<<(llvm::raw_ostream &, const ControlCondition &);
const ControlCondition *getGreatestCommonCondition(const ControlCondition *,
                                                   const ControlCondition *);
const ControlCondition *
    getGreatestCommonCondition(llvm::ArrayRef<const ControlCondition *>);

#endif // CONTROL_DEPENDENCE_H
