#ifndef MATCH_MANAGER_H
#define MATCH_MANAGER_H

#include "InstSema.h"
#include "llvm/IR/BasicBlock.h"
#include <algorithm>

// This class pulls all operation that we are interested in
// and tries to match all of them while trying to avoid
// matching the same operation twice on the same value
class MatchManager {
  // record matches for each operation
  llvm::DenseMap<const Operation *, std::vector<Operation::Match>> OpMatches;

  void match(llvm::Value *V) {
    for (auto &KV : OpMatches) {
      const Operation *Op = KV.first;
      Op->match(V, KV.second);
    }
  }

  static bool sortByOutput(const Operation::Match &A,
                           const Operation::Match &B) {
    return A.Output < B.Output;
  }

public:
  MatchManager(llvm::ArrayRef<InstBinding *> Insts, llvm::BasicBlock &BB) {
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

  llvm::ArrayRef<Operation::Match> getMatches(const Operation *Op) const {
    auto It = OpMatches.find(Op);
    assert(It != OpMatches.end());
    return It->second;
  }

  llvm::ArrayRef<Operation::Match> getMatchesForOutput(const Operation *Op,
                                                       llvm::Value *Output) const {
    auto Matches = getMatches(Op);
    Operation::Match DummyMatch{false, {}, Output};
    auto LowerIt = std::lower_bound(Matches.begin(), Matches.end(), DummyMatch,
                                    sortByOutput);
    auto UpperIt = std::upper_bound(Matches.begin(), Matches.end(), DummyMatch,
                                    sortByOutput);
    return Matches.slice(LowerIt - Matches.begin(), UpperIt - LowerIt);
  }
};

#endif // end MATCH_MANAGER_H
