#include "Embedding.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"
#include <cmath>
#include <functional>

using namespace llvm;

Constant *AffineEmbedder::evaluate(Instruction *Out,
                                   std::vector<Value *> LiveIns,
                                   std::vector<Constant *> LiveInVals) const {
  DenseMap<Value *, Constant *> Values;
  assert(LiveIns.size() == LiveInVals.size());
  for (unsigned i = 0; i < LiveIns.size(); i++) {
    Values[LiveIns[i]] = LiveInVals[i];
  }

  std::function<Constant *(Value *)> Evaluate = [&](Value *V) -> Constant * {
    if (auto *C = dyn_cast<Constant>(V))
      return C;

    auto It = Values.find(V);
    if (It != Values.end())
      return It->second;

    auto *I = cast<Instruction>(V);
    std::vector<Constant *> Operands;
    for (Value *O : I->operands()) {
      Operands.push_back(Evaluate(O));
    }

    //////////
    errs() << "Evaluating " << *I << ": [";
    for (unsigned i = 0; i < I->getNumOperands(); i++) {
      errs() << *I->getOperand(i) << " -> " << *Operands[i] << ", ";
    }
    errs() << "]\n";
    ///////////

    Constant *C;
    if (auto *Cmp = dyn_cast<CmpInst>(I)) 
      C = ConstantFoldCompareInstOperands(
          Cmp->getPredicate(),
          Operands[0], Operands[1], *DL);
    else
      C = ConstantFoldInstOperands(I, Operands, *DL);
    return Values[V] = C;
  };
  return Evaluate(Out);
}

// Get the values alive in the beginning of this `BB` and reachable to `I`
static std::vector<Value *> getLiveIns(Instruction *I, BasicBlock *BB) {
  std::vector<Value *> LiveIns;
  DenseSet<Value *> Seen;

  std::function<void(Value *)> GetLiveIns = [&](Value *V) {
    if (isa<Constant>(V))
      return;

    bool Inserted = Seen.insert(V).second;
    if (!Inserted)
      return;

    auto *I = dyn_cast<Instruction>(V);
    // TODO: make function call a live-ins
    if (!I || I->getParent() != BB || isa<LoadInst>(I)) {
      LiveIns.push_back(V);
      return;
    }

    for (Value *O : I->operands())
      GetLiveIns(O);
  };

  GetLiveIns(I);
  return LiveIns;
}

// Embed an expression by evaluating it with the unit vectors
Optional<Embedding> AffineEmbedder::embed(Instruction *I, bool Signed) const {
  assert(I->getType()->isIntegerTy() || I->getType()->isFloatingPointTy() ||
         "can only embed numeric values");
  std::vector<Value *> LiveIns = getLiveIns(I, BB);
  std::vector<Constant *> Zeros;
  for (auto *V : LiveIns)
    Zeros.push_back(Constant::getNullValue(V->getType()));

  Embedding E(S);
  for (unsigned i = 0; i < LiveIns.size(); i++) {
    auto *V = LiveIns[i];
    auto *Ty = V->getType();
    bool IsInt = Ty->isIntegerTy();
    auto X = Zeros;
    X[i] = IsInt ? ConstantInt::get(Ty, 1) : ConstantFP::get(Ty, 1.);
    Constant *Y = evaluate(I, LiveIns, X);
    if (!Y)
      return Optional<Embedding>();
    errs() << "!!! EVALUATED " << *I << " TO " << *Y
      << " (" << cast<ConstantInt>(Y)->getSExtValue()
      << ")\n";
    if (auto *CI = dyn_cast<ConstantInt>(Y))
      E.push_back(Signed ? (float)CI->getSExtValue() : (float)CI->getZExtValue());
    else
      E.push_back(cast<ConstantFP>(Y)->getValueAPF().convertToFloat());
  }
  std::sort(E.begin(), E.end());
  return E;
}

static float square(float x) {
  return x*x;
}

float Embedding::operator-(const Embedding &E2) const {
  auto &E1 = *this;
  assert(E1.size() == E2.size());

  float N = E1.size();
  float DiffSqr = 0;
  for (unsigned i = 0; i < N; i++) {
    DiffSqr += square(E1[i] - E2[i]);
  }
  return S * std::sqrtf(DiffSqr / 3.0);
}

llvm::raw_ostream &operator<<(llvm::raw_ostream &OS, const Embedding &E) {
  OS << '[';
  for (float x : E) {
    OS << x << ',';
  }
  OS << ']';
  return OS;
}
