#include "RenameAllocas.h"
#include "LoopAwareRPO.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/PatternMatch.h"

using namespace llvm;
using namespace PatternMatch;

namespace {
// Track the lifetime of an alloca
struct Lifetime {
  CallInst *Begin, *End;
  // (indirect) User of the alloca during that lifetime
  SmallPtrSet<Instruction *, 4> Users;
};
} // namespace

static bool findLifetimes(DominatorTree &DT, PostDominatorTree &PDT,
                          LoopInfo &LI, AliasAnalysis &AA, const DataLayout &DL,
                          AllocaInst *Alloca,
                          SmallVectorImpl<Lifetime> &Lifetimes) {
  auto MaybeSize = Alloca->getAllocationSizeInBits(DL);
  if (!MaybeSize)
    return false;
  uint64_t Size = *MaybeSize / 8;
  auto BeginPat = m_Intrinsic<Intrinsic::lifetime_start>(
      m_ConstantInt(Size), m_BitCast(m_Specific(Alloca)));
  auto EndPat = m_Intrinsic<Intrinsic::lifetime_end>(
      m_ConstantInt(Size), m_BitCast(m_Specific(Alloca)));

  SmallVector<BasicBlock *> RPO;
  computeRPO(Alloca->getFunction(), LI, RPO);
  CallInst *Begin = nullptr;
  SmallPtrSet<Instruction *, 4> Users;
  for (auto *BB : RPO) {
    for (auto &I : *BB) {
      if (BeginPat.match(&I)) {
        // Bail in the unlikely case when we see an overlapping pattern
        if (Begin)
          return false;
        Begin = cast<CallInst>(&I);
        continue;
      }

      if (EndPat.match(&I)) {
        if (!Begin)
          return false;

        // Bail if the lifetime markers are not control-flow equivalent
        if (!DT.dominates(Begin, &I) || !PDT.dominates(&I, Begin))
          return false;

        Lifetimes.push_back({Begin, cast<CallInst>(&I), Users});

        // Start a new lifetime
        Begin = nullptr;
        Users.clear();
        continue;
      }

      // Bail if I uses some pointer that may alias with the alloca and that
      // pointer is not computed within the lifetime
      for (auto *V : I.operand_values())
        if (V != Alloca && AA.alias(V, Alloca) &&
            !Users.count(cast<Instruction>(V)))
          return false;

      if (any_of(I.operand_values(),
                 [Alloca](Value *V) { return V == Alloca; }))
        Users.insert(&I);
    }
  }
  return true;
}

static void reallocateForLifetime(DominatorTree &DT, PostDominatorTree &PDT,
                                  AliasAnalysis &AA, const Lifetime &LT,
                                  AllocaInst *Alloca) {
  auto *NewAlloca =
      new AllocaInst(Alloca->getAllocatedType(), 0, Alloca->getArraySize(),
                     Alloca->getName(), Alloca);
  NewAlloca->setAlignment(Alloca->getAlign());
  for (auto *I : LT.Users)
    I->replaceUsesOfWith(Alloca, NewAlloca);
  auto *Int8PtrTy = Type::getInt8PtrTy(Alloca->getContext());
  assert(LT.Begin->arg_size() == 2);
  LT.Begin->setArgOperand(1,
                          new BitCastInst(NewAlloca, Int8PtrTy, "", LT.Begin));
  assert(LT.End->arg_size() == 2);
  LT.End->setArgOperand(1, new BitCastInst(NewAlloca, Int8PtrTy, "", LT.End));
}

void renameAllocas(DominatorTree &DT, PostDominatorTree &PDT, LoopInfo &LI,
                   AliasAnalysis &AA, const DataLayout &DL,
                   ArrayRef<AllocaInst *> Allocas) {
  for (auto *Alloca : Allocas) {
    // Only deal with the default address space
    if (Alloca->getType()->getAddressSpace() != 0)
      continue;

    SmallVector<Lifetime, 8> Lifetimes;
    bool Ok = findLifetimes(DT, PDT, LI, AA, DL, Alloca, Lifetimes);
    if (!Ok)
      continue;
    for (auto &LT : drop_begin(Lifetimes))
      reallocateForLifetime(DT, PDT, AA, LT, Alloca);
  }
}
