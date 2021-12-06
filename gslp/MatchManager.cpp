#include "MatchManager.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/IR/InstIterator.h"

using namespace llvm;

bool MatchManager::sortByOutput(const Operation::Match &A,
                                const Operation::Match &B) {
  return A.Output < B.Output;
}

void MatchManager::match(Value *V) {
  for (auto &KV : OpMatches) {
    const Operation *Op = KV.first;
    Op->match(V, KV.second);
  }
}

MatchManager::MatchManager(ArrayRef<const InstBinding *> Insts,
                           Function &F) {
  for (auto &Inst : Insts)
    for (auto &LaneOp : Inst->getLaneOps())
      OpMatches.FindAndConstruct(LaneOp.getOperation());

  for (auto &I : instructions(&F))
    match(&I);

  for (auto &KV : OpMatches) {
    auto &Matches = KV.second;
    std::sort(Matches.begin(), Matches.end(), sortByOutput);
  }
}

MatchManager::MatchManager(ArrayRef<const InstBinding *> Insts,
                           ArrayRef<Instruction *> ToMatch) {
  for (auto &Inst : Insts)
    for (auto &LaneOp : Inst->getLaneOps())
      OpMatches.FindAndConstruct(LaneOp.getOperation());

  for (auto *I : ToMatch)
    match(I);

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
                                  Value *Output) const {
  auto Matches = getMatches(Op);
  Operation::Match DummyMatch{false, {}, Output};
  auto LowerIt = std::lower_bound(Matches.begin(), Matches.end(), DummyMatch,
                                  sortByOutput);
  auto UpperIt = std::upper_bound(Matches.begin(), Matches.end(), DummyMatch,
                                  sortByOutput);
  return Matches.slice(LowerIt - Matches.begin(), UpperIt - LowerIt);
}
