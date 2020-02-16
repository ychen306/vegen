#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/PatternMatch.h"

using namespace llvm;
using namespace PatternMatch;

namespace {

/////////////// begin data structure for the generalized packing problem 
struct InstSignature {
  std::vector<unsigned> InputBitwidths;
  std::vector<unsigned> OutputBitwidths;
  bool HasImm8;
};

struct InputSlice {
  const InstSignature &Sig;
  unsigned InputId;
  unsigned Lo, Hi;
};

// Interface that abstractly defines an operation
struct Operation {
  virtual bool numLiveins() const = 0;
  // `match' returns true if `V` is matched.
  // If a match is found, additionally return the matched liveins
  virtual bool match(Value *V, std::vector<Value *> &MatchedLiveIns) const = 0;
};

// Interface describing output of a vector lane, which is 
// either 1) simply a copy of an input slice.
// or 2) an operation (BoundOperation)
class SliceCopy;
class BoundOperation;
struct LaneDescription {
  virtual const SliceCopy *getSliceCopy() const { return nullptr; }
  virtual const BoundOperation *getBoundOperation() const { return nullptr; }
};

// Excplicit copy of an input slice
class SliceCopy : public LaneDescription {
  InputSlice CopiedSlice;
public:
  SliceCopy(InputSlice S) : CopiedSlice(S) {}
  const SliceCopy *getSliceCopy() const override { return this; }
  const InputSlice &getCopiedSlice() const { return CopiedSlice; }
};

// An operation explicitly bound to an instruction and its input(s)
class BoundOperation : public LaneDescription {
  const Operation *Operation;
  std::vector<InputSlice> BoundSlices;
public:
  const BoundOperation *getBoundOperation() const override { return this; }
  // A bound operation
  BoundOperation(
      const struct Operation *Operation, 
      std::vector<InputSlice> BoundSlices) :
    Operation(Operation), BoundSlices(BoundSlices) {}
};

// An instruction is a list of lanes,
// each of which characterized by a BoundOperation
class InstBinding {
  std::vector<LaneDescription> Lanes;
public:
  InstBinding(std::vector<LaneDescription> Lanes) : Lanes(Lanes) {}
};
///////////// end

class GSLP : public FunctionPass {
public:
  static char ID; // Pass identification, replacement for typeid
  GSLP() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override;
};

template <typename PRED_TY, typename LHS_TY, typename RHS_TY, typename PAT_TY>
PAT_TY m_c_ICmp_dont_care(PRED_TY Pred, LHS_TY LHS, RHS_TY RHS) {
  return m_c_ICmp(Pred, LHS, RHS);
}

bool hasBitWidth(const Value *V, unsigned BitWidth) {
  auto *Ty = V->getType();
  if (Ty->isIntegerTy())
    return Ty->getIntegerBitWidth() == BitWidth;
  if (Ty->isFloatTy())
    return BitWidth == 32;
  if (Ty->isDoubleTy())
    return BitWidth == 64;
  return false;
}

} // end anonymous namespace

char GSLP::ID = 0;

bool GSLP::runOnFunction(Function &F) {
  return false;
}

// Automatically enable the pass.
// http://adriansampson.net/blog/clangpass.html
static void registerGSLP(const PassManagerBuilder &,
                         legacy::PassManagerBase &PM) {
  PM.add(new GSLP());
}
static RegisterStandardPasses
  RegisterMyPass(PassManagerBuilder::EP_VectorizerStart,
                 registerGSLP);
