#include "ShuffleOpt.h"
#include "llvm/IR/Instructions.h"

using namespace llvm;

// Canonicalize a shufflevector so that its first operand is V
static void canonicalize(ShuffleVectorInst *SV, const Value *V) {
  if (SV->getOperand(0) == V)
    return;
  if (SV->getOperand(1) != V)
    errs() << "???????? " << *SV << ", " << *V << '\n';
  assert(SV->getOperand(1) == V);
  SV->commute();
}

bool mergeShuffleVectors(ShuffleVectorInst *SV1, ShuffleVectorInst *SV2) {
  if (SV1->getParent() != SV2->getParent())
    return false;

  // Make a *copy* of the masks of SV1 and SV2
  const std::vector<int> Mask1 = SV1->getShuffleMask(), Mask2 = SV2->getShuffleMask();
  if (Mask1.size() != Mask2.size())
    return false;

  for (User *U : SV1->users())
    if (!isa<ShuffleVectorInst>(U))
      return false;
  for (User *U : SV2->users())
    if (!isa<ShuffleVectorInst>(U))
      return false;

  if (!SV1->comesBefore(SV2)) {
    auto *t = SV1;
    SV1 = SV2;
    SV2 = t;
    //std::swap(SV1, SV2);
  }

  // Canonicalize SV2 so that it has the same operand order as SV1
  if (SV1->getOperand(0) != SV2->getOperand(0))
    SV2->commute();
  if (SV1->getOperand(0) != SV2->getOperand(0) ||
      SV1->getOperand(1) != SV2->getOperand(1))
    return false;

  errs() << "???? MERGING " << *SV1 << " AND " << *SV2 << '\n';

  Value *VecA = SV1->getOperand(0), *VecB = SV1->getOperand(1);
  assert(isa<FixedVectorType>(VecA->getType()));
  assert(isa<FixedVectorType>(VecB->getType()));

  // Size of the source vectors we are gathering from
  unsigned N = cast<FixedVectorType>(VecA->getType())->getNumElements();
  // Figure out the elements we are gathering.
  SmallVector<unsigned> A, B;
  auto ProcessMaskValue = [&A, &B, N](unsigned X) {
    if (X == UndefMaskElem)
      return;
    if (X < N)
      A.push_back(X);
    else
      B.push_back(X - N);
  };
  for (int X : Mask1)
    ProcessMaskValue(X);
  for (int X : Mask2)
    ProcessMaskValue(X);

  // Can't coalesce if we can't fit the elements of A and B
  //  into a vector of the same size of the old shufflevector
  if (A.size() + B.size() > Mask1.size())
    return false;

  std::sort(A.begin(), A.end());
  std::sort(B.begin(), B.end());

  // Build the new mask by interleaving values of A & B
  SmallVector<int> NewMask;
  bool TakeA = true;
  unsigned Ai = 0, Bi = 0; // index of A & B
  std::vector<unsigned> NewDestOfA(N), NewDestOfB(N);
  auto TakeOneFromA = [&]() {
    assert(Ai < A.size());
    NewDestOfA[A[Ai]] = NewMask.size();
    NewMask.push_back(A[Ai]);
    ++Ai;
  };
  auto TakeOneFromB = [&]() {
    assert(Bi < B.size());
    NewDestOfB[B[Bi]] = NewMask.size();
    NewMask.push_back(B[Bi] + N);
    ++Bi;
  };
  // mapping value of A to its new destination in the new shuffle vector
  while (Ai < A.size() && Bi < B.size()) {
    if (TakeA)
      TakeOneFromA();
    else
      TakeOneFromB();
    TakeA = !TakeA;
  }
  while (Ai < A.size())
    TakeOneFromA();
  while (Bi < B.size())
    TakeOneFromB();
  assert(NewMask.size() <= Mask1.size());
  // Pad the mask with undefs if we need to
  NewMask.resize(Mask1.size(), UndefMaskElem);

  auto FixUserMasks = [&](ShuffleVectorInst *SV, ArrayRef<int> OldSVMask) {
    unsigned i = 0;
    assert(SV->getNumUses() == std::distance(SV->user_begin(), SV->user_end()));
    std::vector<User *> Users(SV->user_begin(), SV->user_end());
    for (auto *U : Users) {
      errs() << "iter = " << i++ << '\n';
      errs() << "??? num users of " << SV << " is " << SV->getNumUses() << '\n';
      auto *UserSV = cast<ShuffleVectorInst>(U);
      assert(UserSV->getOperand(0) == SV || UserSV->getOperand(1) == SV);
      canonicalize(UserSV, SV);
      if (UserSV == SV)
        abort();
      assert(UserSV != SV);
      std::vector<int> Mask = UserSV->getShuffleMask();
      for (int &X : Mask) {
        if (X == UndefMaskElem || X >= OldSVMask.size())
          continue;
        int NewX;
        if (OldSVMask[X] == UndefMaskElem)
          NewX = UndefMaskElem;
        else if (OldSVMask[X] < N) {
          assert(OldSVMask[X] < NewDestOfA.size());
          NewX = NewDestOfA[OldSVMask[X]];
        } else {
          assert(OldSVMask[X]-N < NewDestOfB.size());
          NewX = NewDestOfB[OldSVMask[X]-N];
        }
        assert(OldSVMask[X] == UndefMaskElem || NewMask[NewX] == OldSVMask[X]);
        X = NewX;
      }
      assert(cast<FixedVectorType>(UserSV->getType())->getNumElements() == Mask.size());
      UserSV->setShuffleMask(Mask);
    }
  };

  FixUserMasks(SV1, Mask1);
  FixUserMasks(SV2, Mask2);

  // Use the new mask
  SV1->setShuffleMask(NewMask);
  SV2->replaceAllUsesWith(SV1);
  assert(SV2->user_begin() == SV2->user_end());
  SV2->eraseFromParent();
  return true;
}
