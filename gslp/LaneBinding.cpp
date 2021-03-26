#include "LaneBinding.h"

using namespace llvm;

LaneBinding::LaneBinding(const InstBinding *Inst) {
  auto &Sig = Inst->getSignature();
  unsigned NumInputs = Sig.numInputs();
  auto LaneOps = Inst->getLaneOps();
  unsigned NumLanes = LaneOps.size();

  Inputs.resize(NumInputs);

  struct BoundInput {
    InputSlice Slice;
    InputRef X;

    // Order by offset of the slice
    bool operator<(const BoundInput &Other) const {
      return Slice < Other.Slice;
    }
  };

  // Figure out which input packs we need
  for (unsigned i = 0; i < NumInputs; i++) {
    std::vector<BoundInput> InputValues;
    // Find output lanes that uses input `i` and record those uses
    for (unsigned j = 0; j < NumLanes; j++) {
      ArrayRef<InputSlice> BoundSlices = LaneOps[j].getBoundSlices();
      for (unsigned k = 0; k < BoundSlices.size(); k++) {
        auto &BS = BoundSlices[k];
        if (BS.InputId != i)
          continue;
        InputValues.push_back({BS, InputRef(j, k)});
      }
    }

    // Sort the input values by their slice offset
    std::sort(InputValues.begin(), InputValues.end());

    unsigned CurOffset = 0;
    unsigned Stride = InputValues[0].Slice.size();
    auto &Input = Inputs[i];
    for (const BoundInput &BV : InputValues) {
      while (CurOffset < BV.Slice.Lo) {
        Input.push_back(None);
        CurOffset += Stride;
      }
      assert(CurOffset == BV.Slice.Lo);
      Input.push_back(BV.X);
      CurOffset += Stride;
    }
    unsigned InputSize = Sig.InputBitwidths[i];
    while (CurOffset < InputSize) {
      Input.push_back(None);
      CurOffset += Stride;
    }
    assert(Input.size() * Stride == InputSize);
  }
}

void LaneBinding::apply(unsigned i, LaneBinding::MatchList Matches,
                        SmallVectorImpl<Value *> &Input) const {
  Input.clear();
  for (const Optional<InputRef> &M : Inputs[i])
    Input.push_back(M ? M->get(Matches) : nullptr);
}
