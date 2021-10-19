#include "Packer.h"
#include "CodeMotionUtil.h"
#include "ConsecutiveCheck.h"
#include "ControlEquivalence.h"
#include "MatchManager.h"
#include "VectorPack.h"
#include "llvm/Analysis/LoopInfo.h"
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
    for (auto Pair : ConsecutiveAccesses)
      DAG[Pair.first].insert(Pair.second);
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

Packer::Packer(ArrayRef<const InstBinding *> Insts, Function &F,
               AliasAnalysis *AA, LoopInfo *LI, ScalarEvolution *SE,
               DominatorTree *DT, PostDominatorTree *PDT, DependenceInfo *DI,
               LazyValueInfo *LVI, TargetTransformInfo *TTI,
               BlockFrequencyInfo *BFI,
               EquivalenceClasses<BasicBlock *> *UnrolledBlocks,
               bool Preplanning)
    : F(&F), VPCtx(&F), DA(*AA, *SE, *DT, *LI, *LVI, &F, &VPCtx, Preplanning),
      CDA(*LI, *DT, *PDT), LDA(*AA, *DI, *SE, *DT, *LI, *LVI),

      TopVL(*LI, &VPCtx, DA, CDA, LoopToVLoopMap),

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

      if (BO.comesBefore(L2, L1))
        std::swap(L1, L2);

      if (!DA.getDepended(L2).test(VPCtx.getScalarId(L1)))
        EquivalentValues.unionSets(L1, L2);
    }
  }
  errs() << "finished looking for equivalent loads\n";
  VPCtx.registerEquivalentValues(std::move(EquivalentValues));
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

// Assuming all elements of `OP` are loads, try to find an extending load pack.
static void findExtendingLoadPacks(const OperandPack &OP, Packer *Pkr,
                                   SmallVectorImpl<VectorPack *> &Extensions) {
  auto *VPCtx = Pkr->getContext();
  auto &LoadDAG = Pkr->getLoadDAG();
  auto &DA = Pkr->getDA();

  // The set of loads producing elements of `OP`
  SmallPtrSet<Instruction *, 8> LoadSet;
  for (auto *V : OP) {
    if (!V)
      continue;
    if (auto *I = dyn_cast<Instruction>(V))
      LoadSet.insert(I);
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
  return all_of(drop_begin(Cmps), [&](auto *Cmp) {
    return Cmp->getOpcode() == Opcode && Cmp->getPredicate() == Pred;
  });
}

static bool matchPackableGEPs(ArrayRef<Value *> Values,
                              SmallVectorImpl<GetElementPtrInst *> &GEPs) {
  GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(Values.front());
  if (!GEP)
    return false;
  GEPs.push_back(GEP);
  unsigned NumOperands = GEP->getNumOperands();
  Type *Ty = GEP->getSourceElementType();

  for (auto *V : drop_begin(Values)) {
    auto *GEP2 = dyn_cast<GetElementPtrInst>(V);
    if (GEP2->getNumOperands() != NumOperands ||
        GEP2->getSourceElementType() != Ty)
      return false;
    GEPs.push_back(GEP2);
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
    // TODO: add a pack to disable gathers?
    SmallVector<LoadInst *, 8> Loads;
    // FIXME: make sure the loads have the same type?
    for (auto *V : *OP)
      Loads.push_back(cast<LoadInst>(V));
    OPI.LoadProducers.push_back(
        VPCtx.createLoadPack(Loads, getConditionPack(Loads), Elements, Depended,
                             TTI, true /*is gather*/));
    if (OPI.LoadProducers.empty())
      OPI.Feasible = false;
    return OPI;
  }

  if (AllPHIs) {
    SmallVector<PHINode *> PHIs;
    unsigned NumIncomings = cast<PHINode>(OP->front())->getNumIncomingValues();
    for (auto *V : *OP) {
      // Don't bother pack phis with different number of incomings
      auto *PN = cast<PHINode>(V);
      if (PN->getNumIncomingValues() != NumIncomings) {
        OPI.Feasible = false;
        return OPI;
      }
      PHIs.push_back(PN);
    }
    bool AllEtas = all_of(PHIs, [&](auto *PN) {
      auto *VL = getVLoopFor(PN);
      return VL && VL->getEta(PN);
    });
    bool Convergent = true;
    for (unsigned i = 0; i < NumIncomings; i++) {
      SmallVector<const ControlCondition *> EdgeConds;
      for (auto *PN : PHIs)
        EdgeConds.push_back(
            getEdgeCondition(PN->getIncomingBlock(i), PN->getParent()));
      if (!is_splat(EdgeConds))
        Convergent = false;
    }

    if (Convergent || AllEtas) {
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

  for (auto *Inst : getInsts()) {
    ArrayRef<BoundOperation> LaneOps = Inst->getLaneOps();
    if (LaneOps.size() < NumLanes)
      continue;

    std::vector<const Operation::Match *> Lanes;
    for (unsigned i = 0; i < NumLanes; i++) {
      ArrayRef<Operation::Match> Matches =
          MM.getMatchesForOutput(LaneOps[i].getOperation(), (*OP)[i]);
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
  if (isa<GetElementPtrInst>(I) || isa<PHINode>(I))
    return 0;
  if (!isScalarType(I->getType()))
    return 1;
  if (!isa<BinaryOperator>(I) && !isa<CmpInst>(I) && !isa<SelectInst>(I))
    return 1;
  SmallVector<const Value *, 4> Operands(I->operand_values());
  return TTI->getArithmeticInstrCost(
      I->getOpcode(), I->getType(), TTI::TCK_RecipThroughput, TTI::OK_AnyValue,
      TTI::OK_AnyValue, TTI::OP_None, TTI::OP_None, Operands, I);
}

bool Packer::isCompatible(Instruction *I1, Instruction *I2) {
  if (I1->getParent() == I2->getParent())
    return true;
  return VLoop::isSafeToFuse(getVLoopFor(I1), getVLoopFor(I2), *SE);
}

VLoop *Packer::getVLoopFor(Instruction *I) {
  auto *L = LI->getLoopFor(I->getParent());
  return LoopToVLoopMap.lookup(L);
}

void Packer::fuseLoops(VLoop *VL1, VLoop *VL2) {
  VLoop::fuse(VL1, VL2, LoopToVLoopMap);
}
