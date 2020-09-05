#include "MatchManager.h"
#include "llvm/IR/PatternMatch.h"
#include "Util.h"

using namespace llvm;

// E.g., the intermediate instruction(s) of `(a + b) + c` is `a+b`.
void getIntermediateInsts(const Operation::Match &M,
                          SmallPtrSetImpl<Instruction *> &Intermediates) {
  SmallPtrSet<Value *, 4> LiveIns;
  for (auto *V : M.Inputs)
    LiveIns.insert(V);

  std::function<void(Instruction *)> CollectIntermediates =
      [&](Instruction *I) {
        if (LiveIns.count(I))
          return;
        Intermediates.insert(I);
        for (Value *O : I->operands())
          if (auto *OI = dyn_cast<Instruction>(O))
            CollectIntermediates(OI);
      };

  CollectIntermediates(cast<Instruction>(M.Output));
}

static bool hasExternalUses(const Operation::Match &M) {
  SmallPtrSet<Instruction *, 2> Intermediates;
  getIntermediateInsts(M, Intermediates);
  for (auto *I : Intermediates) {
    if (I == M.Output)
      continue;
    for (User *U : I->users()) {
      auto *UI = dyn_cast<Instruction>(U);
      if (UI && UI != M.Output && !Intermediates.count(UI)) {
        return true;
      }
    }
  }

  return false;
}

bool MatchManager::sortByOutput(const Operation::Match &A,
                                const Operation::Match &B) {
  return A.Output < B.Output;
}

void MatchManager::match(llvm::Value *V) {
  for (auto &KV : OpMatches) {
    const Operation *Op = KV.first;
    Op->match(V, KV.second);
  }
}

MatchManager::MatchManager(llvm::ArrayRef<InstBinding *> Insts,
                           llvm::BasicBlock &BB) {
  for (auto &Inst : Insts)
    for (auto &LaneOp : Inst->getLaneOps())
      OpMatches.FindAndConstruct(LaneOp.getOperation());
  for (auto &I : BB) {
    match(&I);
  }

  for (auto &KV : OpMatches) {
    auto &Matches = KV.second;

#if 0
    // Filter out matches with intermediates that have external uses
    std::vector<unsigned> ToRemove;
    for (unsigned i = 0; i < Matches.size(); i++)
      if (hasExternalUses(Matches[i]))
        ToRemove.push_back(i);
    remove(Matches, ToRemove);
    errs() << " REMOVING " << ToRemove.size() << '\n';
#endif

    std::sort(Matches.begin(), Matches.end(), sortByOutput);
  }
}

ArrayRef<Operation::Match> MatchManager::getMatches(const Operation *Op) const {
  auto It = OpMatches.find(Op);
  assert(It != OpMatches.end());
  return It->second;
}

ArrayRef<Operation::Match>
MatchManager::getMatchesForOutput(const Operation *Op,
                                  llvm::Value *Output) const {
  auto Matches = getMatches(Op);
  Operation::Match DummyMatch{false, {}, Output};
  auto LowerIt = std::lower_bound(Matches.begin(), Matches.end(), DummyMatch,
                                  sortByOutput);
  auto UpperIt = std::upper_bound(Matches.begin(), Matches.end(), DummyMatch,
                                  sortByOutput);
  return Matches.slice(LowerIt - Matches.begin(), UpperIt - LowerIt);
}
