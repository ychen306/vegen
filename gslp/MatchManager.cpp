#include "MatchManager.h"
#include "llvm/IR/PatternMatch.h"
#include "Util.h"

using namespace llvm;

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

MatchManager::MatchManager(llvm::ArrayRef<const InstBinding *> Insts,
                           llvm::BasicBlock &BB) {
  for (auto &Inst : Insts)
    for (auto &LaneOp : Inst->getLaneOps())
      OpMatches.FindAndConstruct(LaneOp.getOperation());
  for (auto &I : BB)
    match(&I);

  for (auto &KV : OpMatches) {
    auto &Matches = KV.second;

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
