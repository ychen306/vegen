#include "Solver.h"
#include "Heuristic.h"
#include "Packer.h"
#include "Plan.h"
#include "VectorPackSet.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Support/CommandLine.h"

using namespace llvm;

static cl::opt<bool>
    RefinePlans("refine-plans",
                cl::desc("Refine the initial vectorization plan"),
                cl::init(false));

unsigned getBitWidth(Value *V, const DataLayout *DL) {
  auto *Ty = V->getType();
  if (Ty->isIntegerTy())
    return Ty->getIntegerBitWidth();
  if (Ty->isFloatTy())
    return 32;
  if (Ty->isDoubleTy())
    return 64;
  auto *PtrTy = dyn_cast<PointerType>(Ty);
  assert(PtrTy && "unsupported value type");
  return DL->getPointerSizeInBits(PtrTy->getAddressSpace());
}

template <typename AccessType>
VectorPack *createMemPack(const VectorPackContext *VPCtx,
                          ArrayRef<AccessType *> Accesses,
                          const BitVector &Elements, const BitVector &Depended,
                          TargetTransformInfo *TTI);

template <>
VectorPack *createMemPack(const VectorPackContext *VPCtx,
                          ArrayRef<StoreInst *> Stores,
                          const BitVector &Elements, const BitVector &Depended,
                          TargetTransformInfo *TTI) {
  return VPCtx->createStorePack(Stores, Elements, Depended, TTI);
}

template <>
VectorPack *createMemPack(const VectorPackContext *VPCtx,
                          ArrayRef<LoadInst *> Loads, const BitVector &Elements,
                          const BitVector &Depended, TargetTransformInfo *TTI) {
  return VPCtx->createLoadPack(Loads, Elements, Depended, TTI);
}

template <typename AccessType>
std::vector<VectorPack *>
getSeedMemPacks(Packer *Pkr, AccessType *Access, unsigned VL,
                DenseSet<BasicBlock *> *BlocksToIgnore) {
  auto &DA = Pkr->getDA();
  auto *VPCtx = Pkr->getContext();
  auto *TTI = Pkr->getTTI();
  bool IsStore = std::is_same<AccessType, StoreInst>::value;
  auto &AccessDAG = IsStore ? Pkr->getStoreDAG() : Pkr->getLoadDAG();

  std::vector<VectorPack *> Seeds;

  auto &LI = Pkr->getLoopInfo();
  std::function<void(std::vector<AccessType *>, BitVector, BitVector)>
      Enumerate = [&](std::vector<AccessType *> Accesses, BitVector Elements,
                      BitVector Depended) {
        if (Accesses.size() == VL) {
          Seeds.push_back(createMemPack<AccessType>(VPCtx, Accesses, Elements,
                                                    Depended, TTI));
          return;
        }

        auto It = AccessDAG.find(Accesses.back());
        if (It == AccessDAG.end()) {
          return;
        }
        for (auto *Next : It->second) {
          if (!IsStore && LI.getLoopFor(Next->getParent()) !=
                              LI.getLoopFor(Accesses.back()->getParent()))
            continue;
          if (BlocksToIgnore && BlocksToIgnore->count(Next->getParent()))
            continue;
          auto *NextAccess = cast<AccessType>(Next);
          if (!checkIndependence(DA, *VPCtx, NextAccess, Elements, Depended))
            continue;

#if 0
          auto CompatibleWithNext = [&](Instruction *I) {
            return Pkr->isControlCompatible(I, NextAccess);
          };
          if (!all_of(Accesses, CompatibleWithNext))
            continue;
#endif
          if (!Pkr->isControlCompatible(Accesses.front(), NextAccess))
            continue;

          auto AccessesExt = Accesses;
          auto ElementsExt = Elements;
          auto DependedExt = Depended;
          AccessesExt.push_back(NextAccess);
          ElementsExt.set(VPCtx->getScalarId(NextAccess));
          DependedExt |= DA.getDepended(NextAccess);
          Enumerate(AccessesExt, ElementsExt, DependedExt);
        }
      };

  std::vector<AccessType *> Accesses{Access};
  BitVector Elements(VPCtx->getNumValues());
  BitVector Depended(VPCtx->getNumValues());

  Elements.set(VPCtx->getScalarId(Access));
  Depended |= DA.getDepended(Access);

  Enumerate(Accesses, Elements, Depended);
  return Seeds;
}

std::vector<const VectorPack *>
enumerate(Packer *Pkr, DenseSet<BasicBlock *> *BlocksToIgnore) {
  auto &DA = Pkr->getDA();
  auto *VPCtx = Pkr->getContext();
  auto &LayoutInfo = Pkr->getStoreInfo();

  auto *TTI = Pkr->getTTI();

  std::vector<const VectorPack *> Packs;
  for (Instruction &I : instructions(Pkr->getFunction())) {
    if (BlocksToIgnore && BlocksToIgnore->count(I.getParent()))
      continue;

    auto *LI = dyn_cast<LoadInst>(&I);
    // Only pack scalar load
    if (!LI || LI->getType()->isVectorTy())
      continue;
    unsigned AS = LI->getPointerAddressSpace();
    unsigned MaxVF = TTI->getLoadStoreVecRegBitWidth(AS) /
                     getBitWidth(LI, Pkr->getDataLayout());
    for (unsigned VL : {64, 32, 16, 8, 4, 2}) {
      if (VL > MaxVF)
        continue;
      for (auto *VP : getSeedMemPacks(Pkr, LI, VL, BlocksToIgnore))
        Packs.push_back(VP);
    }
  }
  return Packs;
}

bool Print = false;

// Run the bottom-up heuristic starting from `OP`
void runBottomUpFromOperand(const OperandPack *OP, Plan &P, Heuristic &H) {
  // Plan Best = P;
  SmallVector<const OperandPack *> Worklist;
  Worklist.push_back(OP);
  SmallPtrSet<const OperandPack *, 4> Visited;
  while (!Worklist.empty()) {
    assert(P.verifyCost());
    auto *OP = Worklist.pop_back_val();

    if (!Visited.insert(OP).second)
      continue;

    // The packs we are adding
    SmallVector<const VectorPack *, 4> NewPacks = H.solve(OP).Packs;
    // The packs we are replacing
    SmallPtrSet<const VectorPack *, 4> OldPacks;

    for (const VectorPack *VP : NewPacks)
      for (auto *V : VP->elementValues())
        if (auto *VP2 = P.getProducer(dyn_cast<Instruction>(V)))
          OldPacks.insert(VP2);

    for (auto *VP2 : OldPacks)
      P.remove(VP2);
    for (const VectorPack *VP : NewPacks) {
      P.add(VP);
      ArrayRef<const OperandPack *> Operands = VP->getOperandPacks();
      Worklist.append(Operands.begin(), Operands.end());
    }
    // if (P.cost() < Best.cost())
    //  Best = P;
  }
  // P = Best;
}

SmallVector<const OperandPack *> deinterleave(const VectorPackContext *VPCtx,
                                              const OperandPack *OP,
                                              unsigned Stride) {
  SmallVector<const OperandPack *> Results;
  for (unsigned i = 0; i < Stride; i++) {
    OperandPack OP2;
    for (unsigned j = i; j < OP->size(); j += Stride)
      OP2.push_back((*OP)[j]);
    Results.push_back(VPCtx->getCanonicalOperandPack(OP2));
  }
  return Results;
}

static const OperandPack *concat(const VectorPackContext *VPCtx,
                                 ArrayRef<Value *> A, ArrayRef<Value *> B) {
  OperandPack Concat;
  Concat.append(A.begin(), A.end());
  Concat.append(B.begin(), B.end());
  return VPCtx->getCanonicalOperandPack(Concat);
}

static const OperandPack *interleave(const VectorPackContext *VPCtx,
                                     ArrayRef<Value *> A, ArrayRef<Value *> B) {
  OperandPack Interleaved;
  assert(A.size() == B.size());
  for (unsigned i = 0; i < A.size(); i++) {
    Interleaved.push_back(A[i]);
    Interleaved.push_back(B[i]);
  }
  return VPCtx->getCanonicalOperandPack(Interleaved);
}

static BasicBlock *getBlockForPack(const VectorPack *VP) {
  for (auto *V : VP->elementValues())
    if (auto *I = dyn_cast<Instruction>(V))
      return I->getParent();
  llvm_unreachable("not block for pack");
}

// decompose a store pack to packs that fit in native bitwidth
static SmallVector<const VectorPack *>
decomposeStorePacks(Packer *Pkr, const VectorPack *VP) {
  assert(VP->isStore());
  auto *BB = getBlockForPack(VP);
  auto *VPCtx = Pkr->getContext();
  ArrayRef<Value *> Values = VP->getOrderedValues();
  auto *SI = cast<StoreInst>(Values.front());
  unsigned AS = SI->getPointerAddressSpace();
  auto *TTI = Pkr->getTTI();
  unsigned VL = TTI->getLoadStoreVecRegBitWidth(AS) /
                getBitWidth(SI->getValueOperand(), Pkr->getDataLayout());
  auto &DA = Pkr->getDA();
  if (Values.size() <= VL)
    return {VP};
  SmallVector<const VectorPack *> Decomposed;
  for (unsigned i = 0, N = Values.size(); i < N; i += VL) {
    SmallVector<StoreInst *> Stores;
    BitVector Elements(VPCtx->getNumValues());
    BitVector Depended(VPCtx->getNumValues());
    for (unsigned j = i; j < std::min(i + VL, N); j++) {
      auto *SI = cast<StoreInst>(Values[j]);
      Stores.push_back(SI);
      Elements.set(VPCtx->getScalarId(SI));
      Depended |= DA.getDepended(SI);
    }
    Decomposed.push_back(
        VPCtx->createStorePack(Stores, Elements, Depended, TTI));
  }
  return Decomposed;
}

static void improvePlan(Packer *Pkr, Plan &P,
                        ArrayRef<const OperandPack *> SeedOperands,
                        CandidatePackSet *Candidates,
                        DenseSet<BasicBlock *> *BlocksToIgnore) {
  SmallVector<const VectorPack *> Seeds;
  for (Instruction &I : instructions(Pkr->getFunction())) {
    auto *SI = dyn_cast<StoreInst>(&I);
    // Only pack scalar store
    if (!SI || SI->getValueOperand()->getType()->isVectorTy())
      continue;
    for (unsigned VL : {2, 4, 8, 16, 32, 64})
      for (auto *VP : getSeedMemPacks(Pkr, SI, VL, BlocksToIgnore)) {
        Seeds.push_back(VP);
      }
  }

  AccessLayoutInfo &LayoutInfo = Pkr->getStoreInfo();
  stable_sort(Seeds, [&](const VectorPack *VP1, const VectorPack *VP2) {
    if (VP1->numElements() != VP2->numElements())
      return VP1->numElements() > VP2->numElements();
    auto *SI1 = cast<StoreInst>(VP1->getOrderedValues().front());
    auto *SI2 = cast<StoreInst>(VP2->getOrderedValues().front());
    auto Info1 = LayoutInfo.get(SI1);
    auto Info2 = LayoutInfo.get(SI2);
    return Info1.Id < Info2.Id;
  });

  auto &LI = Pkr->getLoopInfo();
  auto *TTI = Pkr->getTTI();
  auto *VPCtx = Pkr->getContext();
  // Add reduction packs
  for (auto &I : instructions(Pkr->getFunction())) {
    auto *PN = dyn_cast<PHINode>(&I);
    if (!PN)
      continue;
    Optional<ReductionInfo> RI = matchLoopReduction(PN, LI);
    if (RI && RI->Elts.size() > 1)
      Seeds.push_back(VPCtx->createReduction(*RI, TTI));
  }

  if (Candidates)
    Seeds.append(Candidates->Packs.begin(), Candidates->Packs.end());

  Heuristic H(Pkr, Candidates);

  auto Improve = [&](Plan P2, ArrayRef<const OperandPack *> OPs) -> bool {
    for (auto *OP : OPs) {
      if (!H.solve(OP).Packs.empty())
        runBottomUpFromOperand(OP, P2, H);
    }
    if (P2.cost() < P.cost()) {
      P = P2;
      return true;
    }
    return false;
  };

  DenseMap<const VectorPack *, SmallVector<const VectorPack *>>
      DecomposedStores;

  for (auto *VP : Seeds)
    if (VP->isStore())
      DecomposedStores[VP] = decomposeStorePacks(Pkr, VP);

  auto IsPacked = [&P](auto *V) {
    auto *I = dyn_cast<Instruction>(V);
    return I && P.getProducer(I);
  };

  for (auto *VP : Seeds) {
    if (any_of(VP->elementValues(), IsPacked))
      continue;

    Plan P2 = P;

    if (VP->isStore()) {
      for (auto *VP2 : DecomposedStores[VP])
        P2.add(VP2);
    } else {
      P2.add(VP);
    }

    if (VP->isLoad()) {
      if (P2.cost() < P.cost()) {
        P = P2;
        errs() << "~COST: " << P.cost() << '\n';
      }
      continue;
    }

    auto *OP = VP->getOperandPacks().front();
    if (Improve(P2, {OP}) || Improve(P2, deinterleave(VPCtx, OP, 2)) ||
        Improve(P2, deinterleave(VPCtx, OP, 4)) ||
        Improve(P2, deinterleave(VPCtx, OP, 8))) {
      errs() << "~COST: " << P.cost() << '\n';
    }
  }

  for (auto *OP : SeedOperands) {
    Plan P2 = P;
    if (Improve(P2, {OP}) || Improve(P2, deinterleave(VPCtx, OP, 2)) ||
        Improve(P2, deinterleave(VPCtx, OP, 4)) ||
        Improve(P2, deinterleave(VPCtx, OP, 8))) {
      errs() << "~COST: " << P.cost() << '\n';
    }
  }

  if (!RefinePlans)
    return;

  bool Optimized;
  do {
    errs() << "COST: " << P.cost() << '\n';
    Optimized = false;
    for (auto I = P.operands_begin(), E = P.operands_end(); I != E; ++I) {
      const OperandPack *OP = I->first;
      Plan P2 = P;
      if (Improve(P2, {OP}) || Improve(P2, deinterleave(VPCtx, OP, 2)) ||
          Improve(P2, deinterleave(VPCtx, OP, 4)) ||
          Improve(P2, deinterleave(VPCtx, OP, 8))) {
        Optimized = true;
        break;
      }
    }
    if (Optimized)
      continue;
    errs() << "??? finding good concats, num operands = "
           << std::distance(P.operands_begin(), P.operands_end()) << '\n';
    for (auto I = P.operands_begin(), E = P.operands_end(); I != E; ++I) {
      for (auto J = P.operands_begin(); J != E; ++J) {
        const OperandPack *OP = I->first;
        const OperandPack *OP2 = J->first;
        auto *Concat = concat(VPCtx, *OP, *OP2);
        Plan P2 = P;
        if (Improve(P2, {Concat})) {
          Optimized = true;
          break;
        }
      }
      if (Optimized)
        break;
    }
    errs() << "~~~~~~ done\n";
    if (Optimized)
      continue;

    for (auto *VP : Seeds) {
      Plan P2 = P;
      for (auto *V : VP->elementValues())
        if (auto *VP2 = P2.getProducer(cast<Instruction>(V)))
          P2.remove(VP2);
      for (auto *VP2 : DecomposedStores[VP])
        P2.add(VP2);
      auto *OP = VP->getOperandPacks().front();
      if (Improve(P2, {OP}) || Improve(P2, deinterleave(VPCtx, OP, 2)) ||
          Improve(P2, deinterleave(VPCtx, OP, 4)) ||
          Improve(P2, deinterleave(VPCtx, OP, 8))) {
        Optimized = true;
        break;
      }
    }
  } while (Optimized);
}

float optimizeBottomUp(std::vector<const VectorPack *> &Packs, Packer *Pkr,
                       ArrayRef<const OperandPack *> SeedOperands,
                       DenseSet<BasicBlock *> *BlocksToIgnore) {
  CandidatePackSet Candidates;
  Candidates.Packs = enumerate(Pkr, BlocksToIgnore);
  auto *VPCtx = Pkr->getContext();
  Candidates.Inst2Packs.resize(VPCtx->getNumValues());
  for (auto *VP : Candidates.Packs)
    for (unsigned i : VP->getElements().set_bits())
      Candidates.Inst2Packs[i].push_back(VP);

  Plan P(Pkr);
  improvePlan(Pkr, P, SeedOperands, &Candidates, BlocksToIgnore);
  Packs.insert(Packs.end(), P.begin(), P.end());
  return P.cost();
}

float optimizeBottomUp(VectorPackSet &PackSet, Packer *Pkr,
                       ArrayRef<const OperandPack *> SeedOperands) {
  std::vector<const VectorPack *> Packs;
  float Cost = optimizeBottomUp(Packs, Pkr, SeedOperands);
  for (auto *VP : Packs)
    PackSet.tryAdd(VP);
  return Cost;
}
