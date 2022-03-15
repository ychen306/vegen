#include "Reduction.h"
#include "llvm/InitializePasses.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Pass.h"

using namespace llvm;

namespace llvm {
void initializeVectorCombinerPass(PassRegistry &);
}

namespace {
struct VectorCombiner : public FunctionPass {
  static char ID;
  VectorCombiner() : FunctionPass(ID) {
    initializeVectorCombinerPass(*PassRegistry::getPassRegistry());
  }
  bool runOnFunction(Function &) override;
};

} // namespace

char VectorCombiner::ID = 0;

static Value *matchOrOfExtract(Instruction *I) {
  using namespace PatternMatch;
  if (I->getOpcode() != Instruction::Or)
    return nullptr;

  auto RI = matchLoopFreeReduction(I);
  if (!RI)
    return nullptr;

  Value *Vec = nullptr;
  SmallVector<uint64_t, 8> Idxs;
  if (!match(RI->Elts.front(), m_ExtractElt(m_Value(Vec), m_ConstantInt(Idxs.emplace_back()))))
    return nullptr;
  for (auto *V : drop_begin(RI->Elts))
    if (!match(V, m_ExtractElt(m_Specific(Vec), m_ConstantInt(Idxs.emplace_back()))))
      return nullptr;

  auto *VecTy = dyn_cast<FixedVectorType>(Vec->getType());
  if (!VecTy || VecTy->getNumElements() != RI->Elts.size())
    return nullptr;

  std::sort(Idxs.begin(), Idxs.end());
  bool IsIdentity = true;
  if (Idxs.front() != 0)
    IsIdentity = false;
  for (unsigned i = 1; i < Idxs.size(); i++)
    if (Idxs[i] != Idxs[i-1]+1) {
      IsIdentity = false;
      break;
    }

  if (IsIdentity)
    return Vec;

  IRBuilder<> Builder(I);
  SmallVector<int, 8> Mask(Idxs.begin(), Idxs.end());
  return Builder.CreateShuffleVector(Vec, Mask);
}

bool VectorCombiner::runOnFunction(Function &F) {
  bool Changed = false;
  for (auto &BB : F) {
    auto Insts = make_range(BB.rbegin(), BB.rend());
    for (auto &I : Insts) {
      if (auto *Vec = matchOrOfExtract(&I)) {
        IRBuilder<> Builder(&I);
        auto *Or = Builder.CreateOrReduce(Vec);
        I.replaceAllUsesWith(Or);
        Changed = true;
      }
    }
  }
  return Changed;
}

Pass *createVectorCombiner() { return new VectorCombiner(); }

INITIALIZE_PASS_BEGIN(VectorCombiner, "vector-combiner",
                      "Combine vector shuffle instructions", false, false)
INITIALIZE_PASS_END(VectorCombiner, "vector-combiner",
                    "Combine vector shuffle instructions", false, false)
