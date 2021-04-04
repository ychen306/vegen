#ifndef LANE_BINDING_H
#define LANE_BINDING_H

#include "InstSema.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/SmallVector.h"

namespace llvm {
class Value;
}

class LaneBinding {
public:
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
    unsigned getMatchIdx() const { return MatchIdx; }
    unsigned getInputIdx() const { return InputIdx; }
  };

  using Input = llvm::SmallVector<llvm::Optional<InputRef>, 8>;
private:
  std::vector<Input> Inputs;

public:
  LaneBinding(const InstBinding *);
  unsigned getNumInputs() const { return Inputs.size(); }
  void apply(unsigned i, MatchList,
             llvm::SmallVectorImpl<llvm::Value *> &) const;
  // label how input `i` is used by some input lane, None if not used
  using Label = llvm::Optional<unsigned>;
  void label(unsigned i, llvm::SmallVectorImpl<Label> &) const;
  const Input &getInput(unsigned i) const { return Inputs[i]; }
};
#endif // end LANE_BINDING_H
