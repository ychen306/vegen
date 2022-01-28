#include "Solver.h"
#include "Heuristic.h"
#include "Packer.h"
#include "Plan.h"
#include "VectorPackSet.h"
#include "llvm/Analysis/LoopInfo.h"
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
VectorPack *createMemPack(Packer *Pkr, ArrayRef<AccessType *> Accesses,
                          const BitVector &Elements, const BitVector &Depended,
                          TargetTransformInfo *TTI);

template <>
VectorPack *createMemPack(Packer *Pkr, ArrayRef<StoreInst *> Stores,
                          const BitVector &Elements, const BitVector &Depended,
                          TargetTransformInfo *TTI) {
  return Pkr->getContext()->createStorePack(
      Stores, Pkr->getConditionPack(Stores), Elements, Depended, TTI);
}

template <>
VectorPack *createMemPack(Packer *Pkr, ArrayRef<LoadInst *> Loads,
                          const BitVector &Elements, const BitVector &Depended,
                          TargetTransformInfo *TTI) {
  return Pkr->getContext()->createLoadPack(Loads, Pkr->getConditionPack(Loads),
                                           Elements, Depended, TTI);
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
          // Make sure we can compute the addresses speculatively if we are
          // doing masked load/stores
          auto *AddrComp =
              dyn_cast<Instruction>(Accesses.front()->getPointerOperand());
          SmallVector<Instruction *, 8> AccessInsts(Accesses.begin(),
                                                    Accesses.end());
          if (AddrComp &&
              !Pkr->canSpeculateAt(
                  AddrComp, Pkr->findSpeculationCond(AddrComp, AccessInsts))) {
            return;
          }

          Seeds.push_back(createMemPack<AccessType>(Pkr, Accesses, Elements,
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
          if (!checkIndependence(DA, *VPCtx, NextAccess, Elements, Depended)) {
            continue;
          }
          if (any_of(Accesses, [&](auto *Access) {
                return !Pkr->isCompatible(Access, NextAccess);
              }))
            continue;

          auto AccessesExt = Accesses;
          auto ElementsExt = Elements;
          auto DependedExt = Depended;
          AccessesExt.push_back(NextAccess);
          ElementsExt.set(VPCtx->getScalarId(NextAccess));
          DependedExt |= DA.getDepended(NextAccess);
          Enumerate(AccessesExt, ElementsExt, DependedExt);
          break;
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
void runBottomUpFromOperand(
    const OperandPack *OP, Plan &P, Heuristic &H, bool OverrideExisting,
    std::function<void(const VectorPack *,
                       llvm::SmallVectorImpl<const OperandPack *> &)>
        GetExtraOperands) {
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

    if (!OverrideExisting && !OldPacks.empty())
      continue;

    for (auto *VP2 : OldPacks)
      P.remove(VP2);
    for (const VectorPack *VP : NewPacks) {
      P.add(VP);
      ArrayRef<const OperandPack *> Operands = VP->getOperandPacks();
      Worklist.append(Operands.begin(), Operands.end());
      if (GetExtraOperands)
        GetExtraOperands(VP, Worklist);
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
    Decomposed.push_back(VPCtx->createStorePack(
        Stores, Pkr->getConditionPack(Stores), Elements, Depended, TTI));
  }
  return Decomposed;
}

static unsigned greatestPowerOfTwoDivisor(unsigned n) {
  return (n & (~(n - 1)));
}

static bool haveIdenticalTripCountsAux(Value *A, Value *B, Packer *Pkr) {
  auto *I1 = cast<Instruction>(A);
  auto *I2 = cast<Instruction>(B);
  auto *VL1 = Pkr->getVLoopFor(I1);
  auto *VL2 = Pkr->getVLoopFor(I2);
  if (VL1 == VL2)
    return true;
  return VL1->haveIdenticalTripCounts(VL2, Pkr->getSE());
}

// Collect all the back-edge condition packs for packs of values from divergent
// loops
static void
getBackEdgePacks(Packer *Pkr, const Plan &P,
                 SmallPtrSetImpl<const ConditionPack *> &BackEdgePacks) {
  auto *VPCtx = Pkr->getContext();
  for (auto *VP : P) {
    auto Vals = VP->getOrderedValues();
    if (all_of(drop_begin(Vals), [&](Value *V) {
          return !V || haveIdenticalTripCountsAux(Vals.front(), V, Pkr);
        }))
      continue;
    SmallVector<const ControlCondition *, 8> Conds;
    auto *SomeVal = *find_if(Vals, [](Value *V) { return V != nullptr; });
    for (auto *V : Vals)
      Conds.push_back(Pkr->getVLoopFor(cast<Instruction>(V ? V : SomeVal))
                          ->getBackEdgeCond());
    BackEdgePacks.insert(VPCtx->getConditionPack(Conds));
  }
}

void tryPackBackEdgeConds(Packer *Pkr, Plan &P, Heuristic &H) {
  SmallPtrSet<const ConditionPack *, 4> BackEdgePacks;
  getBackEdgePacks(Pkr, P, BackEdgePacks);
  SmallVector<const OperandPack *, 4> OPs;
  for (auto *CP : BackEdgePacks)
    getOperandPacksFromCondition(CP, OPs);
  Plan P2 = P;
  for (auto *OP : OPs)
    runBottomUpFromOperand(OP, P2, H);
  if (P2.cost() <= P.cost())
    P = P2;
}
static void findLoopFreeReductions(SmallVectorImpl<const VectorPack *> &Seeds,
                                   unsigned MaxVecWidth, Function *F,
                                   GlobalDependenceAnalysis &DA,
                                   const VectorPackContext *VPCtx,
                                   const DataLayout *DL,
                                   TargetTransformInfo *TTI) {
  SmallVector<Value *> Worklist;
  for (auto &I : instructions(F)) {
    if (isa<StoreInst>(&I))
      continue;
    if (I.use_empty() &&
        (I.getType()->isVoidTy() || isa<CallInst>(I) || isa<InvokeInst>(I)))
      Worklist.append(I.value_op_begin(), I.value_op_end());
  }

  DenseSet<Value *> Visited;
  while (!Worklist.empty()) {
    auto *Root = Worklist.pop_back_val();
    if (!Visited.insert(Root).second)
      continue;
    Optional<ReductionInfo>(RI) = matchLoopFreeReduction(Root);
    if (RI && RI->Elts.size() % 2 == 0) {
      unsigned RdxLen =
        std::min<unsigned>(greatestPowerOfTwoDivisor(RI->Elts.size()),
            MaxVecWidth / getBitWidth(Root, DL));
      BitVector Depended(VPCtx->getNumValues());
      for (auto *V : RI->Elts)
        if (auto *I2 = dyn_cast<Instruction>(V))
          Depended |= DA.getDepended(I2);
      Seeds.push_back(
          VPCtx->createLoopFreeReduction(*RI, RdxLen, Depended, TTI));
      Worklist.append(RI->Elts);
    } else if (auto *I = dyn_cast<Instruction>(Root)) {
      Worklist.append(I->value_op_begin(), I->value_op_end());
    }
  }
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
    for (unsigned VL : {2, 4, 8 /*, 16, 32, 64*/})
      for (auto *VP : getSeedMemPacks(Pkr, SI, VL, BlocksToIgnore)) {
        Seeds.push_back(VP);
      }
  }

  AccessLayoutInfo &LayoutInfo = Pkr->getStoreInfo();
  stable_sort(Seeds, [&](const VectorPack *VP1, const VectorPack *VP2) -> bool {
    auto *SI1 = cast<StoreInst>(VP1->getOrderedValues().front());
    auto *SI2 = cast<StoreInst>(VP2->getOrderedValues().front());
    unsigned Id1 = LayoutInfo.get(SI1).Id;
    unsigned Id2 = LayoutInfo.get(SI2).Id;
    int NumElems1 = -int(VP1->numElements());
    int NumElems2 = -int(VP2->numElements());
    return std::tie(Id1, NumElems1) < std::tie(Id2, NumElems2);
  });

  auto &LI = Pkr->getLoopInfo();
  auto *TTI = Pkr->getTTI();
  auto *VPCtx = Pkr->getContext();
  unsigned MaxVecWidth = TTI->getLoadStoreVecRegBitWidth(0);
  // Add loop-reduction packs
  for (auto &I : instructions(Pkr->getFunction())) {
    auto *PN = dyn_cast<PHINode>(&I);
    if (!PN)
      continue;
    if (BlocksToIgnore && BlocksToIgnore->count(PN->getParent()))
      continue;
    Optional<ReductionInfo> RI = matchLoopReduction(PN, LI);
    if (RI && RI->Elts.size() % 2 == 0) {
      unsigned RdxLen = std::min<unsigned>(
          greatestPowerOfTwoDivisor(RI->Elts.size()),
          MaxVecWidth / getBitWidth(PN, Pkr->getDataLayout()));
      Seeds.push_back(VPCtx->createLoopReduction(*RI, RdxLen, TTI));
    }
  }
  findLoopFreeReductions(Seeds, MaxVecWidth, Pkr->getFunction(), Pkr->getDA(),
                         VPCtx, Pkr->getDataLayout(), TTI);

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

    if (Improve(P2, VP->getOperandPacks()))
      errs() << "~COST: " << P.cost() << '\n';
  }

  for (auto *OP : SeedOperands) {
    if (any_of(*OP, IsPacked))
      continue;
    Plan P2 = P;
    if (Improve(P2, {OP})/* || Improve(P2, deinterleave(VPCtx, OP, 2)) ||
        Improve(P2, deinterleave(VPCtx, OP, 4)) ||
        Improve(P2, deinterleave(VPCtx, OP, 8))*/) {
      errs() << "~COST: " << P.cost() << '\n';
    }
  }

  tryPackBackEdgeConds(Pkr, P, H);

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

namespace {

template <typename SetTy, typename ElemTy> class EraseOnReturnGuard {
  SetTy &Set;
  ElemTy Elem;

public:
  EraseOnReturnGuard(SetTy &Set, ElemTy Elem) : Set(Set), Elem(Elem) {}
  ~EraseOnReturnGuard() {
    assert(Set.count(Elem));
    Set.erase(Elem);
  }
};

} // namespace

static bool findLoopDepCycle(
    const EquivalenceClasses<VLoop *> &LoopsToFuse,
    GlobalDependenceAnalysis &DA, const VectorPackContext *VPCtx,
    const std::map<Instruction *, SmallVector<Instruction *, 8>> &ExtraDepMap) {
  std::map<VLoop *, BitVector> ExtendedDeps;
  for (auto It = LoopsToFuse.begin(), E = LoopsToFuse.end(); It != E; ++It) {
    for (auto *VL :
         make_range(LoopsToFuse.member_begin(It), LoopsToFuse.member_end())) {
      // Extend the dependences of VL by taking ExtraDepMap into account
      BitVector Depended = VL->getDepended();
      for (auto *V : VPCtx->iter_values(VL->getContained())) {
        auto *I = cast<Instruction>(V);
        auto DepIt = ExtraDepMap.find(I);
        if (DepIt == ExtraDepMap.end())
          continue;
        for (auto *I2 : DepIt->second) {
          unsigned DepId = VPCtx->getScalarId(I2);
          // Ignore I2 if it doesn't introduce new inter-loop dependence
          if (Depended.test(DepId) || VL->contains(I2))
            continue;
          Depended.set(DepId);
          // Assumption: the extra dep map already contains transitive
          // dependences (and consequently we don't need to find the transitive
          // closure)
          Depended |= DA.getDepended(I2);
        }
      }
      ExtendedDeps[VL] = Depended;
    }
  }

  for (auto It = LoopsToFuse.begin(), E = LoopsToFuse.end(); It != E; ++It) {
    if (!It->isLeader())
      continue;
    for (auto MemberIt = LoopsToFuse.member_begin(It),
              MemberE = LoopsToFuse.member_end();
         MemberIt != MemberE; ++MemberIt) {
      auto *VL1 = *MemberIt;
      auto &VL1Deps = ExtendedDeps[VL1];
      auto &VL1Members = VL1->getContained();
      for (auto MemberIt2 = std::next(MemberIt); MemberIt2 != MemberE;
           ++MemberIt2) {
        auto *VL2 = *MemberIt2;
        if (VL1Deps.anyCommon(VL2->getContained()))
          return true;
        if (ExtendedDeps[VL2].anyCommon(VL1Members))
          return true;
      }
    }
  }
  return false;
}

// Detect dependence cycle within the body of a given loop
static bool findDepCycleInLoop(
    VLoop *VL, const DenseMap<Value *, const VectorPack *> &ValueToPackMap,
    const EquivalenceClasses<VLoop *> &LoopsToFuse,
    const std::map<Instruction *, SmallVector<Instruction *, 8>> &ExtraDepMap,
    GlobalDependenceAnalysis &DA, const VectorPackContext *VPCtx, Packer *Pkr) {
  // Use DFS to discover dependence cycle
  using NodeTy = PointerUnion<Value *, const VectorPack *,
                              const ControlCondition *, VLoop *>;
  DenseSet<NodeTy> Processing, Visited;

  auto GetLeaderVL = [&LoopsToFuse](VLoop *VL) {
    auto It = LoopsToFuse.findValue(VL);
    if (It != LoopsToFuse.end())
      return LoopsToFuse.getLeaderValue(VL);
    return VL;
  };
  SmallVector<VLoop *, 8> FusedLoops;
  auto It = LoopsToFuse.findValue(VL);
  if (It != LoopsToFuse.end())
    FusedLoops.assign(LoopsToFuse.member_begin(It), LoopsToFuse.member_end());
  else
    FusedLoops.push_back(VL);

  std::function<bool(NodeTy)> FindCycle = [&](NodeTy Node) -> bool {
    if (!Processing.insert(Node).second)
      return true;
    EraseOnReturnGuard<decltype(Processing), NodeTy> EraseOnReturn(Processing,
                                                                   Node);

    if (!Visited.insert(Node).second)
      return false;

    if (auto *V = Node.dyn_cast<Value *>()) {
      auto *I = dyn_cast<Instruction>(V);
      if (!I)
        return false;

      // If I is contained by a sub loop, treat that sub loop as a whole item
      // (instead of processing the dep of I individually)
      auto *VLOfI = Pkr->getVLoopFor(I);
      if (any_of(FusedLoops,
                 [VLOfI](VLoop *CoVL) { return CoVL->contains(VLOfI); })) {
        return FindCycle(GetLeaderVL(VLOfI));
      }

      // If the (fused) loop doesn't contain this instruction,
      // the instruction must be from a parent loop of VL and is not our
      // concern.
      if (VL->isLoop() &&
          none_of(FusedLoops, [I](VLoop *CoVL) { return CoVL->contains(I); }))
        return false;

      // If this instruction is packed, need to check the pack as a whole
      auto *VP = ValueToPackMap.lookup(V);
      if (VP) {
        return FindCycle(VP);
      }

      // Check data dependence
      if (any_of(VPCtx->iter_values(DA.getDepended(I)), FindCycle))
        return true;

      auto DepIt = ExtraDepMap.find(I);
      if (DepIt != ExtraDepMap.end() && any_of(DepIt->second, FindCycle))
        return true;

      auto *PN = dyn_cast<PHINode>(I);
      auto *VLI = Pkr->getVLoopFor(I);
      if (PN && VLI->isGatedPhi(PN)) {
        for (unsigned i = 0; i < PN->getNumIncomingValues(); i++)
          if (FindCycle(VLI->getIncomingPhiCondition(PN, i)))
            return true;
      }

      // Check control dependence
      return I && FindCycle(Pkr->getVLoopFor(I)->getInstCond(I));
    }

    if (auto *VP = Node.dyn_cast<const VectorPack *>()) {
      // Data dep.
      if (any_of(VP->dependedValues(), FindCycle))
        return true;
      // Control dep.
      for (auto *V : VP->elementValues()) {
        auto *I = dyn_cast<Instruction>(V);
        if (!I)
          continue;
        auto DepIt = ExtraDepMap.find(I);
        if (DepIt != ExtraDepMap.end() && any_of(DepIt->second, FindCycle))
          return true;
        if (FindCycle(Pkr->getVLoopFor(I)->getInstCond(I)))
          return true;
        auto *PN = dyn_cast<PHINode>(V);
        auto *VLI = Pkr->getVLoopFor(I);
        if (PN && VLI->isGatedPhi(PN)) {
          for (unsigned i = 0; i < PN->getNumIncomingValues(); i++)
            if (FindCycle(VLI->getIncomingPhiCondition(PN, i)))
              return true;
        }
      }
      return false;
    }

    if (auto *SubVL = Node.dyn_cast<VLoop *>()) {
      auto It = LoopsToFuse.findValue(SubVL);
      if (It == LoopsToFuse.end()) {
        return FindCycle(SubVL->getLoopCond()) ||
               any_of(VPCtx->iter_values(SubVL->getDepended()), FindCycle);
      }
      assert(LoopsToFuse.getLeaderValue(SubVL) == SubVL);
      auto CoIteratingLoops =
          make_range(LoopsToFuse.member_begin(It), LoopsToFuse.member_end());
      for (auto *CoVL : CoIteratingLoops)
        if (FindCycle(CoVL->getLoopCond()) ||
            any_of(VPCtx->iter_values(CoVL->getDepended()), FindCycle))
          return true;
    }

    assert(Node.is<const ControlCondition *>());
    auto *C = Node.dyn_cast<const ControlCondition *>();
    if (!C)
      return false;
    if (auto *And = dyn_cast<ConditionAnd>(C))
      return FindCycle(And->Cond) || FindCycle(And->Parent);
    auto *Or = cast<ConditionOr>(C);
    return any_of(Or->Conds, FindCycle);
  };

  for (auto &SubVL : VL->getSubLoops())
    if (FindCycle(GetLeaderVL(SubVL.get())))
      return true;

  for (auto *CoVL : FusedLoops)
    if (any_of(CoVL->getInstructions(), FindCycle))
      return true;
  return false;
}

// FIXME: also make sure we the loops that we want to fuse/co-iterate do not
// have dep cycle Make sure a set of packs have neither data nor control
// dependence
bool findDepCycle(ArrayRef<const VectorPack *> Packs, Packer *Pkr,
                  ArrayRef<std::pair<Instruction *, Instruction *>> ExtraDeps) {
  GlobalDependenceAnalysis &DA = Pkr->getDA();
  ControlDependenceAnalysis &CDA = Pkr->getCDA();
  auto *VPCtx = Pkr->getContext();

  // Mapping instruction -> extra deps
  std::map<Instruction *, SmallVector<Instruction *, 8>> ExtraDepMap;
  for (auto &Dep : ExtraDeps) {
    Instruction *I, *Depended;
    std::tie(Depended, I) = Dep;
    ExtraDepMap[I].push_back(Depended);
  }

  // Map instructions to their packs
  DenseMap<Value *, const VectorPack *> ValueToPackMap;
  for (auto *VP : Packs)
    for (auto *V : VP->elementValues())
      ValueToPackMap.insert({V, VP});

  // Figure out the loops that we need to fuse (or co-iterate)
  EquivalenceClasses<VLoop *> LoopsToFuse;
  std::function<void(VLoop *, VLoop *)> MarkLoopsToFuse = [&](VLoop *VL1,
                                                              VLoop *VL2) {
    if (VL1 || VL1 == VL2)
      return;

    assert(VL1 == VL2 &&
           "attempting to fuse loops with different nesting level");
    LoopsToFuse.unionSets(VL1, VL2);
    MarkLoopsToFuse(VL1->getParent(), VL2->getParent());
  };
  for (auto *VP : Packs) {
    auto *VL =
        Pkr->getVLoopFor(cast<Instruction>(*VP->elementValues().begin()));
    for (auto *V : drop_begin(VP->elementValues()))
      MarkLoopsToFuse(VL, Pkr->getVLoopFor(cast<Instruction>(V)));
  }

  // Figure out if there are any dependence cycles among the loops that we want
  // to fuse.
  if (findLoopDepCycle(LoopsToFuse, DA, VPCtx, ExtraDepMap))
    return true;

  // Find dependence cycle loop by loop
  if (findDepCycleInLoop(&Pkr->getTopVLoop(), ValueToPackMap, LoopsToFuse,
                         ExtraDepMap, DA, VPCtx, Pkr))
    return true;
  auto &VLI = Pkr->getVLoopInfo();
  SmallPtrSet<VLoop *, 8> Checked;
  for (auto *L : Pkr->getLoopInfo().getLoopsInPreorder()) {
    auto *VL = VLI.getVLoop(L);
    auto It = LoopsToFuse.findValue(VL);
    if (It != LoopsToFuse.end())
      VL = LoopsToFuse.getLeaderValue(VL);
    if (!Checked.insert(VL).second)
      continue;
    if (findDepCycleInLoop(VL, ValueToPackMap, LoopsToFuse, ExtraDepMap, DA,
                           VPCtx, Pkr))
      return true;
  }
  return false;
}

float optimizeBottomUp(std::vector<const VectorPack *> &Packs, Packer *Pkr,
                       ArrayRef<const OperandPack *> SeedOperands,
                       DenseSet<BasicBlock *> *BlocksToIgnore) {
  CandidatePackSet Candidates;
  // Candidates.Packs = enumerate(Pkr, BlocksToIgnore);
  auto *VPCtx = Pkr->getContext();
  Candidates.Inst2Packs.resize(VPCtx->getNumValues());
  for (auto *VP : Candidates.Packs)
    for (unsigned i : VP->getElements().set_bits())
      Candidates.Inst2Packs[i].push_back(VP);

  Plan P(Pkr);
  float ScalarCost = P.cost();
  improvePlan(Pkr, P, SeedOperands, &Candidates, BlocksToIgnore);
  Packs.insert(Packs.end(), P.begin(), P.end());
  if (findDepCycle(Packs, Pkr)) {
    errs() << "Aborting due to dependence cycle\n";
    Packs.clear();
    return ScalarCost;
  }
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
