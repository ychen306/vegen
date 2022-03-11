#include "Packer.h"
#include "ConsecutiveCheck.h"
#include "MatchManager.h"
#include "VectorPack.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ValueTracking.h" // isSafeToSpeculativelyExecute
#include "llvm/IR/InstIterator.h"

using namespace llvm;

namespace {

bool isScalarType(Type *Ty) {
  return !Ty->isStructTy() && Ty->getScalarType() == Ty;
}

void buildAccessDAG(ConsecutiveAccessDAG &DAG, ArrayRef<Instruction *> Accesses,
                    EquivalenceClasses<Instruction *> &EquivalentAccesses,
                    const DataLayout *DL, ScalarEvolution *SE, LoopInfo *LI) {
  DenseMap<std::pair<Type *, unsigned>, std::vector<Instruction *>>
      AccessesByTypes;
  for (auto *I : Accesses) {
    auto *Ptr = getLoadStorePointerOperand(I);
    assert(Ptr);
    AccessesByTypes[{Ptr->getType(), LI->getLoopDepth(I->getParent())}]
        .push_back(I);
  }

  for (auto &KV : AccessesByTypes) {
    auto ConsecutiveAccesses =
        findConsecutiveAccesses(*SE, *DL, *LI, KV.second, EquivalentAccesses);
    for (auto Pair : ConsecutiveAccesses) {
      DAG[Pair.first].insert(Pair.second);
    }
  }
}

} // end anonymous namespace

BlockOrdering::BlockOrdering(Function *F) {
  ReversePostOrderTraversal<Function *> RPO(F);
  unsigned i = 0;
  for (BasicBlock *BB : RPO)
    Order[BB] = i++;
}

// FIXME: this is broken (comesBefore is *not* a total relation!)
bool BlockOrdering::comesBefore(BasicBlock *BB1, BasicBlock *BB2) const {
  assert(Order.count(BB1) && Order.count(BB2));
  return Order.lookup(BB1) < Order.lookup(BB2);
}

bool BlockOrdering::comesBefore(Instruction *I1, Instruction *I2) const {
  if (I1->getParent() == I2->getParent())
    return I1->comesBefore(I2);
  return comesBefore(I1->getParent(), I2->getParent());
}

static bool isControlEquivalent(ControlDependenceAnalysis &CDA, VLoop *VL1, VLoop *VL2) {
  if (VL1 == VL2)
    return true;

  if (!VL1 || !VL2)
    return false;

  if (!CDA.isEquivalent(VL1->getLoopCond(), VL2->getLoopCond()))
    return false;

  return isControlEquivalent(CDA, VL1->getParent(), VL2->getParent());
}

static bool isControlEquivalent(Packer *Pkr, Instruction *I1, Instruction *I2) {
  auto &CDA = Pkr->getCDA();
  auto *VL1 = Pkr->getVLoopFor(I1);
  auto *VL2 = Pkr->getVLoopFor(I2);
  auto *C1 = VL1->getInstCond(I1);
  auto *C2 = VL2->getInstCond(I2);
  if (!CDA.isEquivalent(C1, C2))
    return false;
  return isControlEquivalent(CDA, VL1, VL2);
}

Packer::Packer(ArrayRef<const InstBinding *> Insts, Function &F,
               AliasAnalysis *AA, LoopInfo *LI, ScalarEvolution *SE,
               DominatorTree *DT, PostDominatorTree *PDT, DependenceInfo *DI,
               LazyValueInfo *LVI, TargetTransformInfo *TTI,
               BlockFrequencyInfo *BFI,
               EquivalenceClasses<BasicBlock *> *UnrolledBlocks,
               bool Preplanning)
    : F(&F), VPCtx(&F), DA(*AA, *SE, *LI, *LVI, &F, &VPCtx, Preplanning),
      CDA(*LI, *DT, *PDT),

      TopVL(*LI, *DT, &VPCtx, DA, CDA, VLI),

      BO(&F), MM(Insts, F), SE(SE), DT(DT), PDT(PDT), LI(LI),
      SupportedInsts(Insts.vec()), LVI(LVI), TTI(TTI), BFI(BFI) {

  for (auto &BB : F) {
    BlockConditions[&BB] = CDA.getConditionForBlock(&BB);
    if (!isa<PHINode>(&BB.front()))
      continue;
    for (auto *Pred : predecessors(&BB))
      EdgeConditions[{Pred, &BB}] = CDA.getConditionForEdge(Pred, &BB);
  }

  std::vector<Instruction *> Loads, Stores;
  for (auto &I : instructions(&F)) {
    if (auto *LI = dyn_cast<LoadInst>(&I)) {
      if (LI->isSimple())
        Loads.push_back(LI);
    } else if (auto *SI = dyn_cast<StoreInst>(&I)) {
      if (SI->isSimple())
        Stores.push_back(SI);
    }
  }

  EquivalenceClasses<Instruction *> EquivalentAccesses;

  buildAccessDAG(LoadDAG, Loads, EquivalentAccesses, getDataLayout(), SE, LI);
  buildAccessDAG(StoreDAG, Stores, EquivalentAccesses, getDataLayout(), SE, LI);
  LoadInfo = AccessLayoutInfo(LoadDAG);
  StoreInfo = AccessLayoutInfo(StoreDAG);

  // FIXME: directly go over equivalence classes of loads...
  // TODO: find more equivalent instructions based on the equivalent loads
  // Find equivalent loads

#if 1
  EquivalenceClasses<Value *> EquivalentValues;
  for (auto I = inst_begin(F), E = inst_end(F); I != E; ++I) {
    auto *L1 = dyn_cast<LoadInst>(&*I);
    if (!L1)
      continue;
    for (auto J = std::next(I); J != E; ++J) {
      auto *L2 = dyn_cast<LoadInst>(&*J);
      if (!L2)
        continue;

      if (!EquivalentAccesses.isEquivalent(L1, L2))
        continue;

      if (!isControlEquivalent(this, L1, L2))
        continue;

      if (BO.comesBefore(L2, L1))
        std::swap(L1, L2);

      if (!DA.getDepended(L2).test(VPCtx.getScalarId(L1)))
        EquivalentValues.unionSets(L1, L2);
    }
  }
  VPCtx.registerEquivalentValues(std::move(EquivalentValues));
#endif

#if 0
  // Canonicalize phi argument order by control condition
  for (auto &BB : F) {
    // Skip header phi
    if (LI->isLoopHeader(&BB))
      continue;
    for (auto &PN : BB.phis()) {
      auto Zipped = zip(PN.blocks(), PN.incoming_values());
      SmallVector<std::pair<BasicBlock *, Value *>> BlockAndVals(Zipped.begin(),
                                                                 Zipped.end());
      stable_sort(BlockAndVals, [this](auto Pair1, auto Pair2) {
        auto *BB1 = Pair1.first;
        auto *BB2 = Pair2.first;
        return compareConditions(getBlockCondition(BB1), getBlockCondition(BB2));
      });
      errs() << "Before: " << PN << '\n';
      for (unsigned i = 0; i < BlockAndVals.size(); i++) {
        PN.setIncomingBlock(i, BlockAndVals[i].first);
        PN.setIncomingValue(i, BlockAndVals[i].second);
      }
      errs( )<< "After: " << PN << '\n';
    }
  }
#endif
}

AccessLayoutInfo::AccessLayoutInfo(const ConsecutiveAccessDAG &AccessDAG) {
  // First pass to find leaders
  DenseSet<Instruction *> Followers;
  for (auto &AccessAndNext : AccessDAG) {
    Instruction *I = AccessAndNext.first;
    for (auto *Next : AccessAndNext.second)
      Followers.insert(Next);
  }

  for (auto &AccessAndNext : AccessDAG) {
    Instruction *Leader = AccessAndNext.first;
    if (Followers.count(Leader))
      continue;
    Info[Leader] = {Leader, 0};
    unsigned Offset = 0;
    auto *Followers = &AccessAndNext.second;
    for (;;) {
      for (auto *Follower : *Followers) {
        Info[Follower] = {Leader, Offset + 1};
      }
      if (Followers->empty())
        break;
      Instruction *Follower = *Followers->begin();
      auto It = AccessDAG.find(Follower);
      if (It == AccessDAG.end())
        break;
      Followers = &It->second;
      Offset += 1;
    }
    MemberCounts[Leader] = Offset;
  }
}

static bool supersedes(VLoop *VL1, const ControlCondition *C1, VLoop *VL2,
                       const ControlCondition *C2) {
  return (VL1 == VL2 || VL1->contains(VL2)) && isImplied(C1, C2);
}

const ControlCondition *
Packer::findSpeculationCond(Instruction *I, ArrayRef<Instruction *> Users) {
  auto *VL = getVLoopFor(I);
  SmallVector<const ControlCondition *, 8> Conds { VL->getInstCond(I) };
  for (auto *U : Users) {
    auto *UserVL = getVLoopFor(U);
    if (VLoop::isSafeToCoIterate(VL, UserVL))
      Conds.push_back(UserVL->getInstCond(U));
    else {
      auto SubLoops = VL->getSubLoops();
      auto It = find_if(SubLoops, [&](auto &SubVL) {
        return SubVL->contains(U);
      });
      assert(It != SubLoops.end());
      Conds.push_back((*It)->getLoopCond());
    }
  }
  return getGreatestCommonCondition(Conds);
}

// Check if we can speculatively compute a value at a given control condition
bool Packer::canSpeculateAt(Value *V, const ControlCondition *C) {
  auto *I = dyn_cast<Instruction>(V);
  if (!I)
    return true;
  // Easy case: no need to speculate because I always executes
  auto *VL = getVLoopFor(I);
  assert(VL);
  if (isImplied(VL->getInstCond(I), C))
    return true;
  if (!isSafeToSpeculativelyExecute(I))
    return false;
  // Check if the operands of I are always available at condition C
  for (Value *O : I->operands()) {
    auto *OI = dyn_cast<Instruction>(O);
    if (!OI)
      continue;
    auto *VLForOI = getVLoopFor(OI);
    if (!supersedes(VLForOI, VLForOI->getInstCond(OI), VL, C))
      return false;
  }
  return true;
}

// Assuming all elements of `OP` are loads, try to find an extending load pack.
static void findExtendingLoadPacks(const OperandPack &OP, Packer *Pkr,
                                   SmallVectorImpl<VectorPack *> &Extensions) {
  auto *VPCtx = Pkr->getContext();
  auto &LoadDAG = Pkr->getLoadDAG();
  auto &DA = Pkr->getDA();

  // The set of loads producing elements of `OP`
  SmallPtrSet<Instruction *, 8> LoadSet;
  SmallVector<Instruction *, 8> LoadInsts;
  for (auto *V : OP) {
    if (!V)
      continue;
    if (auto *I = dyn_cast<Instruction>(V)) {
      LoadInsts.push_back(I);
      LoadSet.insert(I);
    }
  }

  // The loads might jumbled.
  // In other words, any one of the lanes could be the leading load
  for (auto *V : OP) {
    if (!V)
      continue;
    auto *LeadLI = cast<LoadInst>(V);
    BitVector Elements(VPCtx->getNumValues());
    BitVector Depended(VPCtx->getNumValues());
    Elements.set(VPCtx->getScalarId(LeadLI));
    Depended |= DA.getDepended(LeadLI);
    std::vector<LoadInst *> Loads{LeadLI};

    LoadInst *CurLoad = LeadLI;
    while (Elements.count() < LoadSet.size()) {
      auto It = LoadDAG.find(CurLoad);
      // End of the chain
      if (It == LoadDAG.end())
        break;

      LoadInst *NextLI = nullptr;
      // Only use the next load in the load set
      for (auto *Next : It->second) {
        if (LoadSet.count(Next)) {
          NextLI = cast<LoadInst>(Next);
          break;
        }
      }
      if (!NextLI) {
        // load a don't care to fill the gap
        Loads.push_back(nullptr);
        CurLoad = cast<LoadInst>(*It->second.begin());
        continue;
      }
      if (!checkIndependence(DA, *VPCtx, NextLI, Elements, Depended))
        break;
      Loads.push_back(NextLI);
      Elements.set(VPCtx->getScalarId(NextLI));
      Depended |= DA.getDepended(NextLI);
      CurLoad = NextLI;
    }
    if (Elements.count() == LoadSet.size()) {
      // Need to check if we can speculatively compute the address of this load
      // pack
      SmallVector<const ControlCondition *, 8> Conds;
      auto *AddrComp =
          dyn_cast<Instruction>(Loads.front()->getPointerOperand());
      if (AddrComp && !Pkr->canSpeculateAt(
                          AddrComp, Pkr->findSpeculationCond(AddrComp, LoadInsts)))
        return;

      // Pad
      while (Loads.size() < PowerOf2Ceil(OP.size()))
        Loads.push_back(nullptr);
      Extensions.push_back(
          VPCtx->createLoadPack(Loads, Pkr->getConditionPack(Loads), Elements,
                                Depended, Pkr->getTTI()));
      return;
    }
  }
}

static bool matchPackableCmps(ArrayRef<Value *> Values,
                              SmallVectorImpl<CmpInst *> &Cmps) {
  for (auto *V : Values) {
    auto *Cmp = dyn_cast_or_null<CmpInst>(V);
    if (!Cmp)
      return false;
    Cmps.push_back(Cmp);
  }

  auto Opcode = Cmps.front()->getOpcode();
  auto Pred = Cmps.front()->getPredicate();
  auto *Ty = Cmps.front()->getOperand(0)->getType();
  return all_of(drop_begin(Cmps), [&](auto *Cmp) {
    return Cmp->getOpcode() == Opcode && Cmp->getPredicate() == Pred &&
           Cmp->getOperand(0)->getType() == Ty;
  });
}

// Detect isomorphic instructions that we know how to vectorize
static bool matchSIMDPack(ArrayRef<Value *> Values, SmallVectorImpl<Instruction *> &Insts) {
  if (Values.empty())
    return false;

  auto *Leader = dyn_cast<Instruction>(Values.front());
  if (!Leader)
    return false;

  bool Packable = false, IsDRand48 = false;
  if (Leader->getOpcode() == Instruction::FPTrunc) {
    Packable = true;
  } else if (is_drand48(Leader)) {
    if (Values.size() != 4 && Values.size() != 8)
      return false;
    Packable = true;
    IsDRand48 = true;
  }

  if (!Packable)
    return false;

  for (auto *V : Values) {
    auto *I = dyn_cast<Instruction>(V);
    if (!I ||
        I->getOpcode() != Leader->getOpcode() ||
        I->getType() != Leader->getType())
      return false;
    if (IsDRand48 && !is_drand48(I))
      return false;
    Insts.push_back(I);
  }
  return true;
}

static bool matchPackableGEPs(ArrayRef<Value *> Values,
                              SmallVectorImpl<GetElementPtrInst *> &GEPs) {
  GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(Values.front());
  if (!GEP)
    return false;
  GEPs.push_back(GEP);
  unsigned NumOperands = GEP->getNumOperands();
  Type *Ty = GEP->getSourceElementType();

  SmallVector<ConstantInt *> StructOffsets;
  auto *CurTy = Ty;
  for (Value *Idx : drop_begin(GEP->indices())) {
    if (isa<StructType>(CurTy))
      StructOffsets.push_back(cast<ConstantInt>(Idx));
    else
      StructOffsets.push_back(nullptr);
    CurTy = GetElementPtrInst::getTypeAtIndex(CurTy, Idx);
    if (!CurTy)
      return false;
  }

  for (auto *V : drop_begin(Values)) {
    auto *GEP2 = dyn_cast<GetElementPtrInst>(V);
    if (!GEP2 || GEP2->getNumOperands() != NumOperands ||
        GEP2->getSourceElementType() != Ty)
      return false;
    GEPs.push_back(GEP2);
    auto *CurTy = Ty;
    for (auto Item : enumerate(drop_begin(GEP2->indices()))) {
      unsigned i = Item.index();
      Value *Idx = Item.value();
      if (isa<StructType>(CurTy) && StructOffsets[i] != cast<ConstantInt>(Idx))
        return false;
      CurTy = GetElementPtrInst::getTypeAtIndex(CurTy, Idx);
      if (!CurTy)
        return false;
    }
  }
  return true;
}

ArrayRef<Operation::Match> Packer::findMatches(const Operation *O, Value *V) {
  auto Matches = MM.getMatchesForOutput(O, V);
  if (!Matches.empty())
    return Matches;
  if (SecondaryMM)
    return SecondaryMM->getMatchesForOutput(O, V);
  return {};
}

static bool loadingFromDifferentObjects(const OperandPack *OP) {
  return true;
  Value *Obj = nullptr;
  for (auto *V : *OP) {
    auto *LI = dyn_cast<LoadInst>(V);
    if (!LI)
      continue;
    auto Obj2 = getUnderlyingObject(LI->getPointerOperand());
    if (!Obj)
      Obj = Obj2;
    if (Obj != Obj2)
      return true;
  }
  return true;
}

const OperandProducerInfo &Packer::getProducerInfo(const OperandPack *OP) {
  if (OP->OPIValid)
    return OP->OPI;
  OP->OPIValid = true;
  auto &OPI = OP->OPI;
  OPI.Producers.clear();
  OPI.LoadProducers.clear();

  unsigned NumLanes = OP->size();
  BitVector Elements(VPCtx.getNumValues());
  BitVector Depended(VPCtx.getNumValues());
  OPI.Feasible = true;
  bool AllLoads = true;
  bool HasUndef = false;
  bool AllPHIs = true;
  SmallVector<Instruction *> VisitedInsts;
  for (unsigned i = 0; i < NumLanes; i++) {
    auto *V = (*OP)[i];

    AllPHIs &= isa_and_nonnull<PHINode>(V);
    AllLoads &= isa_and_nonnull<LoadInst>(V);

    if (!V) {
      HasUndef = true;
      continue;
    }

    auto *I = dyn_cast<Instruction>(V);
    if (!I)
      continue;

    AllPHIs &= isa<PHINode>(V);

    unsigned InstId = VPCtx.getScalarId(I);
    if (!OPI.Feasible || !checkIndependence(DA, VPCtx, I, Elements, Depended) ||
        any_of(VisitedInsts,
               [&](auto *Visited) { return !isCompatible(I, Visited); }))
      OPI.Feasible = false;
    Elements.set(InstId);
    Depended |= DA.getDepended(I);

    VisitedInsts.push_back(I);
  }

  OPI.Elements = Elements;

  if (!OPI.Feasible || OPI.Elements.count() < 2)
    return OPI;

  if (AllLoads) {
    findExtendingLoadPacks(*OP, this, OPI.LoadProducers);

    if (OPI.LoadProducers.empty() && loadingFromDifferentObjects(OP)) {
      SmallVector<LoadInst *, 8> Loads;
      // FIXME: make sure the loads have the same type?
      for (auto *V : *OP)
        Loads.push_back(cast<LoadInst>(V));
      OPI.LoadProducers.push_back(
          VPCtx.createLoadPack(Loads, getConditionPack(Loads), Elements, Depended,
            TTI, true /*is gather*/));
    }
    if (OPI.LoadProducers.empty()) {
      OPI.Feasible = false;
    }
    return OPI;
  }

  if (AllPHIs) {
    SmallVector<PHINode *> PHIs;
    unsigned NumIncomings = cast<PHINode>(OP->front())->getNumIncomingValues();
    SmallVector<OneHotPhi> OneHots;
    bool AllOneHots = true;
    for (auto *V : *OP) {
      // Don't bother with packing phis with different number of incomings
      auto *PN = cast<PHINode>(V);
      if (PN->getNumIncomingValues() != NumIncomings) {
        OPI.Feasible = false;
        return OPI;
      }

      // Special case for packing one-hot phis
      auto *VL = getVLoopFor(PN);
      if (auto MaybeOneHot = VL->getOneHotPhi(PN)) {
        OneHots.push_back(*MaybeOneHot);
      } else {
        AllOneHots = false;
      }

      PHIs.push_back(PN);
    }

    if (!OneHots.empty()) {
      if (AllOneHots) {
        // Piggy back on the phi pack...
        // FIXME: do this properly
        OPI.Producers.push_back(
            VPCtx.createPhiPack(PHIs, Elements, Depended, TTI));
      } else {
        // Give up if there's a mix of one-hot phis and regular phis
        OPI.Feasible = false;
      }
      return OPI;
    }

    bool AllMus = all_of(PHIs, [&](auto *PN) {
      auto *VL = getVLoopFor(PN);
      return VL && VL->getMu(PN);
    });

    bool Convergent = true;
    if (!AllMus) {
      for (unsigned i = 0; i < NumIncomings; i++) {
        SmallVector<const ControlCondition *> EdgeConds;
        for (auto *PN : PHIs)
          EdgeConds.push_back(
              getEdgeCondition(PN->getIncomingBlock(i), PN->getParent()));
        if (!is_splat(EdgeConds))
          Convergent = false;
      }
    }

    if (Convergent || AllMus) {
      OPI.Producers.push_back(
          VPCtx.createPhiPack(PHIs, Elements, Depended, TTI));
    } else {
      SmallVector<const GammaNode *> Gammas;
      for (auto *PN : PHIs)
        Gammas.push_back(CDA.getGamma(PN));
      OPI.Producers.push_back(
          VPCtx.createGammaPack(Gammas, Elements, Depended, TTI));
    }
    return OPI;
  }

  if (HasUndef) {
    OPI.Feasible = false;
    return OPI;
  }

  SmallVector<CmpInst *, 4> Cmps;
  if (matchPackableCmps(*OP, Cmps)) {
    OPI.Producers.push_back(
        VPCtx.createCmpPack(Cmps, OPI.Elements, Depended, TTI));
    return OPI;
  }

  SmallVector<GetElementPtrInst *, 4> GEPs;
  if (matchPackableGEPs(*OP, GEPs)) {
    OPI.Producers.push_back(
        VPCtx.createGEPPack(GEPs, OPI.Elements, Depended, TTI));
    return OPI;
  }

  SmallVector<Instruction *, 4> Insts;
  if (matchSIMDPack(*OP, Insts)) {
    OPI.Producers.push_back(
        VPCtx.createSIMDPack(Insts, OPI.Elements, Depended, TTI));
  }

  for (auto *Inst : getInsts()) {
    ArrayRef<BoundOperation> LaneOps = Inst->getLaneOps();
    if (LaneOps.size() < NumLanes)
      continue;
    if (LaneOps.size() != NumLanes)
      continue;

    std::vector<const Operation::Match *> Lanes;
    for (unsigned i = 0; i < NumLanes; i++) {
      ArrayRef<Operation::Match> Matches =
          findMatches(LaneOps[i].getOperation(), (*OP)[i]);
      if (Matches.empty())
        break;
      // FIXME: consider multiple matches for the same operation
      Lanes.push_back(&Matches[0]);
    }

    if (Lanes.size() == NumLanes) {
      while (Lanes.size() < LaneOps.size())
        Lanes.push_back(nullptr);
      OPI.Producers.push_back(
          VPCtx.createVectorPack(Lanes, OPI.Elements, Depended, Inst, TTI));
    }
  }
  OPI.Feasible = !OPI.Producers.empty();
  return OPI;
}

float Packer::getScalarCost(Instruction *I) {
  if (auto *LI = dyn_cast<LoadInst>(I)) {
    return TTI->getMemoryOpCost(Instruction::Load, LI->getType(),
                                LI->getAlign(), 0, TTI::TCK_RecipThroughput,
                                LI);
  }

  if (auto *SI = dyn_cast<StoreInst>(I))
    return TTI->getMemoryOpCost(
        Instruction::Store, SI->getValueOperand()->getType(), SI->getAlign(), 0,
        TTI::TCK_RecipThroughput, SI);

  if (auto *CI = dyn_cast<CallInst>(I)) {
    auto *Callee = CI->getCalledFunction();
    if (!Callee)
      return 1;
    auto ID = Callee->getIntrinsicID();
    switch (ID) {
    default:
      return 1;
    case Intrinsic::sin:
    case Intrinsic::cos:
    case Intrinsic::exp:
    case Intrinsic::exp2:
    case Intrinsic::log:
    case Intrinsic::log10:
    case Intrinsic::log2:
    case Intrinsic::fabs:
    case Intrinsic::pow:
      return TTI->getIntrinsicInstrCost(
          IntrinsicCostAttributes(ID, I->getType(), {I->getType()}),
          TTI::TCK_RecipThroughput);
    }
  }

  if (isa<CastInst>(I)) {
    return TTI->getCastInstrCost(I->getOpcode(), I->getOperand(0)->getType(),
                                 I->getType(), TTI::getCastContextHint(I),
                                 TTI::TCK_RecipThroughput);
  }

  if (isa<GetElementPtrInst>(I) || isa<PHINode>(I))
    return 0;
  if (!isScalarType(I->getType()))
    return 1;
  if (!isa<UnaryOperator>(I) && !isa<BinaryOperator>(I) && !isa<CmpInst>(I) &&
      !isa<SelectInst>(I))
    return 1;
  SmallVector<const Value *, 4> Operands(I->operand_values());
  return TTI->getArithmeticInstrCost(
      I->getOpcode(), I->getType(), TTI::TCK_RecipThroughput, TTI::OK_AnyValue,
      TTI::OK_AnyValue, TTI::OP_None, TTI::OP_None, Operands, I);
}

bool Packer::isCompatible(Instruction *I1, Instruction *I2) {
  if (I1->getParent() == I2->getParent())
    return true;
  return VLoop::isSafeToCoIterate(getVLoopFor(I1), getVLoopFor(I2));
}

VLoop *Packer::getVLoopFor(Instruction *I) { return VLI.getLoopForInst(I); }

void Packer::fuseOrCoIterateLoops(VLoop *VL1, VLoop *VL2) {
  if (false && VLoop::isSafeToFuse(VL1, VL2, CDA, *SE))
    VLI.fuse(VL1, VL2);
  else
    VLI.coiterate(VL1, VL2);
}
