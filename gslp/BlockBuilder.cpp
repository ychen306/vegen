#include "BlockBuilder.h"
#include "ControlDependence.h"
#include "llvm/IR/IRBuilder.h"

using namespace llvm;

BlockBuilder::BlockBuilder(
    BasicBlock *EntryBB,
    std::function<llvm::Value *(llvm::Value *)> EmitCondition)
    : Ctx(EntryBB->getContext()), F(EntryBB->getParent()),
      EmitCondition(EmitCondition), ActiveConds({{nullptr, EntryBB}}) {}

BasicBlock *BlockBuilder::createBlock() {
  return BasicBlock::Create(Ctx, "", F);
}

static Value *
emitCondition(const ControlCondition *Common, const ControlCondition *C,
              IRBuilderBase &IRB,
              std::function<llvm::Value *(llvm::Value *)> EmitCondition);
// Emit code that computes the disjunction for Conds at BB
static Value *
emitDisjunction(const ControlCondition *Common,
                ArrayRef<const ControlCondition *> Conds, IRBuilderBase &IRB,
                std::function<llvm::Value *(llvm::Value *)> EmitCondition) {
  SmallVector<Value *> Values;
  for (auto *C : Conds)
    Values.push_back(emitCondition(Common, C, IRB, EmitCondition));
  return IRB.CreateOr(Values);
}

static Value *CreateAnd(Value *A, Value *B, IRBuilderBase &IRB) {
  if (A == ConstantInt::getTrue(IRB.getContext()))
    return B;
  return IRB.CreateAnd(A, B);
}

static Value *
emitCondition(const ControlCondition *Common, const ControlCondition *C,
              IRBuilderBase &IRB,
              std::function<llvm::Value *(llvm::Value *)> EmitCondition) {
  if (C == Common)
    return ConstantInt::getTrue(IRB.getContext());
  assert(C);
  if (auto *And = dyn_cast<ConditionAnd>(C)) {
    return CreateAnd(emitCondition(Common, And->Parent, IRB, EmitCondition),
                     And->IsTrue ? EmitCondition(And->Cond)
                                 : IRB.CreateNot(EmitCondition(And->Cond)),
                     IRB);
  }
  return emitDisjunction(Common, cast<ConditionOr>(C)->Conds, IRB,
                         EmitCondition);
}

// Emit code that computes the disjunction for Conds at BB
static Value *
emitDisjunction(BasicBlock *BB, const ControlCondition *Common,
                ArrayRef<const ControlCondition *> Conds,
                std::function<llvm::Value *(llvm::Value *)> EmitCondition) {
  IRBuilder<> IRB(BB);
  return emitDisjunction(Common, Conds, IRB, EmitCondition);
}

BasicBlock *BlockBuilder::getBlockFor(const ControlCondition *C) {
  if (auto *BB = ActiveConds.lookup(C))
    return BB;

  // Get active conditions that use C and
  // unmark all intermediate semi-active conditions.
  auto GetActiveConds = [&](const ControlCondition *C,
                            SmallPtrSetImpl<const ControlCondition *> &Conds) {
    SmallPtrSet<const ControlCondition *, 4> Visited;
    SmallVector<const ControlCondition *> Worklist{C};
    assert(SemiActiveConds.count(C));
    while (!Worklist.empty()) {
      auto *C2 = Worklist.pop_back_val();
      if (!Visited.insert(C2).second)
        continue;

      if (ActiveConds.count(C2)) {
        Conds.insert(C2);
        continue;
      }

      auto It = SemiActiveConds.find(C2);
      assert(It != SemiActiveConds.end());
      Worklist.append(It->second.begin(), It->second.end());
      SemiActiveConds.erase(It);
    }
  };

  // If C is a semi-active condition,
  // join all of the blocks using C to the block for C
  if (SemiActiveConds.count(C)) {
    SmallPtrSet<const ControlCondition *, 4> Conds;
    GetActiveConds(C, Conds);
    auto *BB = createBlock();
    for (auto *C2 : Conds) {
      auto It = ActiveConds.find(C2);
      assert(It != ActiveConds.end());
      BranchInst::Create(BB, It->second);
      ActiveConds.erase(It);
    }
    ActiveConds[C] = BB;
    return BB;
  }

  if (auto *And = dyn_cast<ConditionAnd>(C)) {
    auto *IfTrue = createBlock();
    auto *IfFalse = createBlock();
    BranchInst::Create(IfTrue, IfFalse, EmitCondition(And->Cond),
                       getBlockFor(And->Parent));
    auto *BB = And->IsTrue ? IfTrue : IfFalse;

    assert(ActiveConds.count(And->Parent));
    ActiveConds.erase(And->Parent);
    SemiActiveConds[And->Parent].assign({And, And->Complement});
    ActiveConds[And] = BB;
    ActiveConds[And->Complement] = And->IsTrue ? IfFalse : IfTrue;
    return BB;
  }

  auto *Or = cast<ConditionOr>(C);

  // If all of the conditions are active, just join all of them.
  if (all_of(Or->Conds, [&](auto *C2) { return ActiveConds.count(C2); })) {
    auto *BB = createBlock();
    for (auto *C2 : Or->Conds) {
      auto It = ActiveConds.find(C2);
      assert(It != ActiveConds.end());
      BranchInst::Create(BB, It->second);
      ActiveConds.erase(It);
      SemiActiveConds[C2] = {C};
    }
    ActiveConds[C] = BB;
    return BB;
  }

  // At this point, we need a join but not all the conditions we want are
  // active. Find all the active blocks that are using the greatest common cond.
  SmallPtrSet<const ControlCondition *, 4> Conds;
  auto *CommonC = Or->GreatestCommonCond;
  if (!SemiActiveConds.count(CommonC)) {
    (void)getBlockFor(CommonC);
    Conds.insert(CommonC);
  } else {
    GetActiveConds(CommonC, Conds);
  }

  // Join the conditions we want to BB.
  // Join the other conditions to AuxBB, which then branch conditionally to BB
  auto *BB = createBlock();
  auto *AuxBB = createBlock();
  SmallPtrSet<const ControlCondition *, 4> CondsToJoin, Joined;
  CondsToJoin.insert(Or->Conds.begin(), Or->Conds.end());
  for (auto *C2 : Conds) {
    auto It = ActiveConds.find(C2);
    assert(It != ActiveConds.end());
    auto *BB2 = It->second;

    if (CondsToJoin.count(C2)) {
      BranchInst::Create(BB, BB2);
      Joined.insert(C2);
    } else {
      BranchInst::Create(AuxBB, BB2);
    }
    ActiveConds.erase(It);
  }

  SmallVector<const ControlCondition *, 4> UnjoinedConds;
  for (auto *C : Or->Conds)
    if (!Joined.count(C))
      UnjoinedConds.push_back(C);

  // Branch conditionally from AuxBB to BB
  auto *DrainBB = createBlock();
  BranchInst::Create(
      BB, DrainBB,
      emitDisjunction(AuxBB, CommonC, UnjoinedConds, EmitCondition), AuxBB);

  // Create a dummy condition that represents the complement of the disjunction.
  auto *DummyC = getDummyCondition();
  ActiveConds[C] = BB;
  ActiveConds[DummyC] = DrainBB;
  SemiActiveConds[CommonC] = {C, DummyC};
  return BB;
}

void BlockBuilder::setBlockForCondition(llvm::BasicBlock *BB,
                                        const ControlCondition *C) {
  assert(ActiveConds.count(C) && "can only set block for active condition");
  ActiveConds[C] = BB;
}

const ControlCondition *BlockBuilder::getDummyCondition() {
  return reinterpret_cast<const ControlCondition *>(DummyCounter++);
}
