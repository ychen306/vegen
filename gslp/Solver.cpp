#include "Solver.h"
#include "Heuristic.h"
#include "Packer.h"
#include "Plan.h"
#include "VectorPackSet.h"

using namespace llvm;

template <typename AccessType>
VectorPack *createMemPack(VectorPackContext *VPCtx,
                          ArrayRef<AccessType *> Accesses,
                          const BitVector &Elements, const BitVector &Depended,
                          TargetTransformInfo *TTI);

template <>
VectorPack *createMemPack(VectorPackContext *VPCtx,
                          ArrayRef<StoreInst *> Stores,
                          const BitVector &Elements, const BitVector &Depended,
                          TargetTransformInfo *TTI) {
  return VPCtx->createStorePack(Stores, Elements, Depended, TTI);
}

template <>
VectorPack *createMemPack(VectorPackContext *VPCtx, ArrayRef<LoadInst *> Loads,
                          const BitVector &Elements, const BitVector &Depended,
                          TargetTransformInfo *TTI) {
  return VPCtx->createLoadPack(Loads, Elements, Depended, TTI);
}

template <typename AccessType>
std::vector<VectorPack *> getSeedMemPacks(Packer *Pkr, BasicBlock *BB,
                                          AccessType *Access, unsigned VL) {
  auto &LDA = Pkr->getLDA(BB);
  auto *VPCtx = Pkr->getContext(BB);
  auto *TTI = Pkr->getTTI();
  bool IsStore = std::is_same<AccessType, StoreInst>::value;
  auto &AccessDAG = IsStore ? Pkr->getStoreDAG(BB) : Pkr->getLoadDAG(BB);

  std::vector<VectorPack *> Seeds;

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
          auto *NextAccess = cast<AccessType>(Next);
          if (!checkIndependence(LDA, *VPCtx, NextAccess, Elements, Depended)) {
            continue;
          }
          auto AccessesExt = Accesses;
          auto ElementsExt = Elements;
          auto DependedExt = Depended;
          AccessesExt.push_back(NextAccess);
          ElementsExt.set(VPCtx->getScalarId(NextAccess));
          DependedExt |= LDA.getDepended(NextAccess);
          Enumerate(AccessesExt, ElementsExt, DependedExt);
        }
      };

  std::vector<AccessType *> Accesses{Access};
  BitVector Elements(VPCtx->getNumValues());
  BitVector Depended(VPCtx->getNumValues());

  Elements.set(VPCtx->getScalarId(Access));
  Depended |= LDA.getDepended(Access);

  Enumerate(Accesses, Elements, Depended);
  return Seeds;
}

std::vector<const VectorPack *> enumerate(BasicBlock *BB, Packer *Pkr) {
  auto &LDA = Pkr->getLDA(BB);
  auto *VPCtx = Pkr->getContext(BB);
  auto &LayoutInfo = Pkr->getStoreInfo(BB);

  std::vector<const VectorPack *> Packs;
  for (auto &I : *BB) {
    if (auto *LI = dyn_cast<LoadInst>(&I)) {
      for (unsigned VL : {2, 4, 8, 16 , 32/*, 64*/})
        for (auto *VP : getSeedMemPacks(Pkr, BB, LI, VL))
          Packs.push_back(VP);
    }
  }
  return Packs;
}

// Run the bottom-up heuristic starting from `OP`
void runBottomUpFromOperand(const OperandPack *OP, Plan &P,
                            const VectorPackContext *VPCtx, Heuristic &H,
                            bool OverridePacked = false) {
  std::vector<const OperandPack *> Worklist{OP};
  while (!Worklist.empty()) {
    assert(P.verifyCost());
    auto *OP = Worklist.back();
    Worklist.pop_back();

    // The packs we are adding
    SmallVector<const VectorPack *, 4> NewPacks = H.solve(OP).Packs;
    // Union of the values covered by this solution
    BitVector Elements(VPCtx->getNumValues());
    // The packs we are replacing
    SmallPtrSet<const VectorPack *, 4> OldPacks;

    for (const VectorPack *VP : NewPacks) {
      Elements |= VP->getElements();
      for (auto *V : VP->elementValues())
        if (auto *VP2 = P.getProducer(dyn_cast<Instruction>(V)))
          OldPacks.insert(VP2);
    }

    bool Feasible = true;
    if (!OverridePacked) {
      // We only consider this solution if
      // the values we are packing is a superset of the
      // values packed in the original plan
      unsigned N = Elements.count();
      for (auto *VP2 : OldPacks)
        if ((Elements |= VP2->getElements()).count() > N) {
          Feasible = false;
          break;
        }
    }
    if (!Feasible)
      continue;

    for (auto *VP2 : OldPacks)
      P.remove(VP2);
    for (const VectorPack *VP : NewPacks) {
      P.add(VP);
      ArrayRef<const OperandPack *> Operands = VP->getOperandPacks();
      Worklist.insert(Worklist.end(), Operands.begin(), Operands.end());
    }
  }
}

SmallVector<const OperandPack *>
deinterleave(const VectorPackContext *VPCtx, const OperandPack *OP, unsigned Stride) {
  SmallVector<const OperandPack *> Results;
  for (unsigned i = 0; i < Stride; i++) {
    OperandPack OP2;
    for (unsigned j = i; j < OP->size(); j += Stride)
      OP2.push_back((*OP)[j]);
    Results.push_back(VPCtx->getCanonicalOperandPack(OP2));
  }
  return Results;
}

static const OperandPack *concat(VectorPackContext *VPCtx, ArrayRef<Value *> A,
                                 ArrayRef<Value *> B) {
  OperandPack Concat;
  Concat.append(A.begin(), A.end());
  Concat.append(B.begin(), B.end());
  return VPCtx->getCanonicalOperandPack(Concat);
}

static const OperandPack *interleave(VectorPackContext *VPCtx,
                                     ArrayRef<Value *> A, ArrayRef<Value *> B) {
  OperandPack Interleaved;
  assert(A.size() == B.size());
  for (unsigned i = 0; i < A.size(); i++) {
    Interleaved.push_back(A[i]);
    Interleaved.push_back(B[i]);
  }
  return VPCtx->getCanonicalOperandPack(Interleaved);
}

// decompose a store pack to packs that fit in native bitwidth
static SmallVector<const VectorPack *> decomposeStorePacks(Packer *Pkr, const VectorPack *VP) {
  assert(VP->isStore());
  auto *VPCtx = VP->getContext();
  SmallVector<const VectorPack *> Decomposed;
  ArrayRef<Value *> Values = VP->getOrderedValues();
  unsigned AS = cast<StoreInst>(Values.front())->getPointerAddressSpace();
  auto *TTI = Pkr->getTTI();
  unsigned VL = TTI->getLoadStoreVecRegBitWidth(AS);
  auto &LDA = Pkr->getLDA(VPCtx->getBasicBlock());
  for (unsigned i = 0, N = Values.size(); i < N; i += VL) {
    SmallVector<StoreInst *> Stores;
    BitVector Elements(VPCtx->getNumValues());
    BitVector Depended(VPCtx->getNumValues());
    for (unsigned j = i; j < N; j++) {
      auto *SI = cast<StoreInst>(Values[j]);
      Stores.push_back(SI);
      Elements.set(VPCtx->getScalarId(SI));
      Depended |= LDA.getDepended(SI);
    }
    Decomposed.push_back(
        VPCtx->createStorePack(Stores, Elements, Depended, TTI));
  }
  return Decomposed;
}

void improvePlan(Packer *Pkr, Plan &P, const CandidatePackSet *CandidateSet) {
  std::vector<const VectorPack *> Seeds;
  auto *BB = P.getBasicBlock();
  for (auto &I : *BB)
    if (auto *SI = dyn_cast<StoreInst>(&I))
      for (unsigned VL : {2, 4, 8, 16, 32})
        for (auto *VP : getSeedMemPacks(Pkr, BB, SI, VL))
          Seeds.push_back(VP);

  auto *VPCtx = Pkr->getContext(P.getBasicBlock());
  Heuristic H(Pkr, VPCtx, CandidateSet);

  auto Improve = [&](Plan P2, ArrayRef<const OperandPack *> OPs,
                     bool Override) -> bool {
    for (auto *OP : OPs)
      runBottomUpFromOperand(OP, P2, VPCtx, H, Override);
    if (P2.cost() < P.cost()) {
      P = P2;
      return true;
    }
    return false;
  };

  DenseMap<const VectorPack *, SmallVector<const VectorPack *>> DecomposedStores;
  for (auto *VP : Seeds)
    DecomposedStores[VP] = decomposeStorePacks(Pkr, VP);

  bool Optimized;
  do {
    errs() << "COST: " << P.cost() << '\n';
    Optimized = false;
    for (auto *VP : Seeds) {
      Plan P2 = P;
      for (auto *V : VP->elementValues())
        if (auto *VP2 = P2.getProducer(cast<Instruction>(V)))
          P2.remove(VP2);
      for (auto *VP2 : DecomposedStores[VP])
        P2.add(VP2);
      auto *OP = VP->getOperandPacks().front();
      auto OP_2 = deinterleave(VPCtx, OP, 2);
      auto OP_4 = deinterleave(VPCtx, OP, 4);
      auto OP_8 = deinterleave(VPCtx, OP, 8);
      if (Improve(P2, {OP}, true) || Improve(P2, {OP}, false) ||
          Improve(P2, OP_2, true) || Improve(P2, OP_2, false) ||
          Improve(P2, OP_4, true) || Improve(P2, OP_4, false) ||
          Improve(P2, OP_8, true) || Improve(P2, OP_8, false)) {
        Optimized = true;
        break;
      }
    }
    if (Optimized)
      continue;
    for (auto I = P.operands_begin(), E = P.operands_end(); I != E; ++I) {
      const OperandPack *OP = I->first;
      auto OP_2 = deinterleave(VPCtx, OP, 2);
      auto OP_4 = deinterleave(VPCtx, OP, 4);
      auto OP_8 = deinterleave(VPCtx, OP, 8);
      Plan P2 = P;
      if (Improve(P2, {OP}, true) || Improve(P2, {OP}, false) ||
          Improve(P2, OP_2, true) || Improve(P2, OP_2, false) ||
          Improve(P2, OP_4, true) || Improve(P2, OP_4, false) ||
          Improve(P2, OP_8, true) || Improve(P2, OP_8, false)) {
        Optimized = true;
        break;
      }
    }
    if (Optimized)
      continue;
    for (auto *VP : P) {
      for (auto *VP2 : P) {
        auto Vals1 = VP->getOrderedValues();
        auto Vals2 = VP2->getOrderedValues();
        if (VP == VP2 || Vals1.size() != Vals2.size() ||
            VP2->getDepended().anyCommon(VP->getElements()) ||
            VP->getDepended().anyCommon(VP2->getElements()))
          continue;
        auto *Concat = concat(VPCtx, Vals1, Vals2);
        auto *Interleaved = interleave(VPCtx, Vals1, Vals2);
        Plan P2 = P;
        P2.remove(VP);
        P2.remove(VP2);
        if (Improve(P2, {Interleaved}, false) ||
            Improve(P2, {Interleaved}, true) || Improve(P2, {Concat}, false) ||
            Improve(P2, {Concat}, true)) {
          Optimized = true;
          break;
        }
      }
      if (Optimized)
        break;
    }
  } while (Optimized);

#ifndef NDEBUG
  Plan P2(Pkr, BB);
  for (auto *VP : P)
    P2.add(VP);
  if (P2.cost() != P.cost())
    errs() << "!!! " << P2.cost() << ", " << P.cost() << '\n';
  assert(P2.cost() == P.cost());

  for (auto I = P.operands_begin(), E = P.operands_end(); I != E; ++I) {
    const OperandPack *OP = I->first;
    bool Foo = false;
    for (auto *V : *OP) {
      auto *I = dyn_cast_or_null<Instruction>(V);
      if (I && !P.getProducer(I)) {
        Foo = true;
        break;
      }
    }
    if (!Foo)
      continue;
    errs() << "op without producer: " << *OP << "\n\t[";
    for (auto *V : *OP) {
      auto *I = dyn_cast_or_null<Instruction>(V);
      if (I && !P.getProducer(I)) {
        errs() << " 0";
      } else
        errs() << " 1";
    }
    errs() << "]\n";
  }
#endif
}

float optimizeBottomUp(VectorPackSet &Packs, Packer *Pkr, BasicBlock *BB) {
  CandidatePackSet CandidateSet;
  CandidateSet.Packs = enumerate(BB, Pkr);
  auto *VPCtx = Pkr->getContext(BB);
  CandidateSet.Inst2Packs.resize(VPCtx->getNumValues());
  for (auto *VP : CandidateSet.Packs)
    for (unsigned i : VP->getElements().set_bits())
      CandidateSet.Inst2Packs[i].push_back(VP);

  Plan P(Pkr, BB);
  improvePlan(Pkr, P, &CandidateSet);
  for (auto *VP : P) {
    Packs.tryAdd(VP);
  }
  return P.cost();
}
