#ifndef LANE_BINDING_H
#define LANE_BINDING_H

#include "InstSema.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/SmallVector.h"

namespace llvm {
class Value;
}

class LaneBinding {
  using MatchList = llvm::ArrayRef<const Operation::Match *>;
  class InputRef {
    unsigned MatchIdx;
    unsigned InputIdx;

  public:
    InputRef(unsigned i, unsigned j) : MatchIdx(i), InputIdx(j) {}
    llvm::Value *get(MatchList Matches) const {
      if (auto *M = Matches[MatchIdx])
        return M->Inputs[InputIdx];
      return nullptr;
    }
  };
  using Input = llvm::SmallVector<llvm::Optional<InputRef>, 8>;
  std::vector<Input> Inputs;

public:
  LaneBinding(const InstBinding *);
  unsigned getNumInputs() const { return Inputs.size(); }
  void apply(unsigned i, MatchList,
             llvm::SmallVectorImpl<llvm::Value *> &) const;
};

#endif // end LANE_BINDING_H
