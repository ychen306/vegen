#include "Packer.h"
#include "CodeMotionUtil.h"
#include "ConsecutiveCheck.h"
#include "MatchManager.h"
#include "ControlEquivalence.h"
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
  DenseMap<std::pair<Type *, unsigned>, std::vector<Instruction *>> AccessesByTypes;
  for (auto *I : Accesses) {
    auto *Ptr = getLoadStorePointerOperand(I);
    assert(Ptr);
    AccessesByTypes[{Ptr->getType(), LI->getLoopDepth(I->getParent())}].push_back(I);
  }

  for (auto &KV : AccessesByTypes) {
    auto ConsecutiveAccesses = findConsecutiveAccesses(*SE, *DL, *LI, KV.second, EquivalentAccesses);
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
               BlockFrequencyInfo *BFI, EquivalenceClasses<BasicBlock *> *UnrolledBlocks, bool IsPreplanning)
    : F(&F), VPCtx(&F),
    DA(IsPreplanning ? nullptr : new GlobalDependenceAnalysis(*AA, *SE, *DT, *LI, *LVI, &F, &VPCtx)),
      LDA(*AA, *DI, *SE, *DT, *LI, *LVI), BO(&F), MM(Insts, F),
      CompatChecker(*LI, *DT, *PDT, LDA, SE, &VPCtx, DA.get(), true /*precompute*/, UnrolledBlocks),
      SE(SE), DT(DT), PDT(PDT), LI(LI), SupportedInsts(Insts.vec()), LVI(LVI),
      TTI(TTI), BFI(BFI), Preplanning(IsPreplanning) {

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

  errs() << "!! looking for equivalent loads\n";
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

      if (Preplanning || !DA->getDepended(L2).test(VPCtx.getScalarId(L1)))
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
  auto *DA = Pkr->getDA();

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
    if (DA)
      Depended |= DA->getDepended(LeadLI);
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
      if (DA && !checkIndependence(*DA, *VPCtx, NextLI, Elements, Depended))
        break;
      Loads.push_back(NextLI);
      Elements.set(VPCtx->getScalarId(NextLI));
      if (DA)
        Depended |= DA->getDepended(NextLI);
      CurLoad = NextLI;
    }
    if (Elements.count() == LoadSet.size()) {
      // Pad
      while (Loads.size() < PowerOf2Ceil(OP.size()))
        Loads.push_back(nullptr);
      Extensions.push_back(
          VPCtx->createLoadPack(Loads, Elements, Depended, Pkr->getTTI()));
      return;
    }
  }
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
    if (!OPI.Feasible || (DA && !checkIndependence(*DA, VPCtx, I, Elements, Depended)))
      OPI.Feasible = false;
    Elements.set(InstId);
    if (DA)
      Depended |= DA->getDepended(I);

    // We can only pack instructions that are control-compatible
    //auto CompatibleWithI = [&](Instruction *I2) {
    //  return isControlCompatible(I, I2);
    //};
    //if (!OPI.Feasible || !all_of(VisitedInsts, CompatibleWithI))
    if (!OPI.Feasible || (!VisitedInsts.empty() && !isControlCompatible(VisitedInsts.front(), I)))
      OPI.Feasible = false;
    VisitedInsts.push_back(I);
  }

  OPI.Elements = std::move(Elements);

  if (!OPI.Feasible || OPI.Elements.count() < 2)
    return OPI;

  if (AllLoads) {
    findExtendingLoadPacks(*OP, this, OPI.LoadProducers);
    if (OPI.LoadProducers.empty())
      OPI.Feasible = false;
    return OPI;
  }

  if (AllPHIs) {
    SmallVector<PHINode *> PHIs;
    for (auto *V : *OP)
      PHIs.push_back(cast<PHINode>(V));
    OPI.Producers.push_back(VPCtx.createPhiPack(PHIs, TTI));
    return OPI;
  }

  if (HasUndef) {
    OPI.Feasible = false;
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

bool Packer::isControlCompatible(Instruction *I1, Instruction *I2) const {
  if (I1->getParent() == I2->getParent())
    return true;

  if (!BO.comesBefore(I1->getParent(), I2->getParent()))
    std::swap(I1, I2);

  if (Preplanning)
    return isControlEquivalent(*I1->getParent(), *I2->getParent(), *DT, *PDT);

  return CompatChecker.isControlCompatible(I2, I1->getParent());
}
