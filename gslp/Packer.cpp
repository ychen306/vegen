#include "Packer.h"
#include "MatchManager.h"

using namespace llvm;

namespace {

bool isScalarType(Type *Ty) { return Ty->getScalarType() == Ty; }

// Do a quadratic search to build the access dags
template <typename MemAccessTy>
void buildAccessDAG(ConsecutiveAccessDAG &DAG, ArrayRef<MemAccessTy *> Accesses,
                    const DataLayout *DL, ScalarEvolution *SE) {
  using namespace llvm;
  for (auto *A1 : Accesses) {
    // Get type of the value being acccessed
    auto *Ty =
        cast<PointerType>(A1->getPointerOperand()->getType())->getElementType();
    if (!isScalarType(Ty))
      continue;
    for (auto *A2 : Accesses) {
      if (A1->getType() == A2->getType() &&
          isConsecutiveAccess(A1, A2, *DL, *SE))
        DAG[A1].insert(A2);
    }
  }
}

} // end anonymous namespace

Packer::Packer(ArrayRef<InstBinding *> SupportedInsts, Function &F,
               AliasAnalysis *AA, const DataLayout *DL, ScalarEvolution *SE,
               TargetTransformInfo *TTI, BlockFrequencyInfo *BFI)
    : F(&F), SupportedInsts(SupportedInsts.vec()), TTI(TTI), BFI(BFI) {
  // Setup analyses and determine search space
  for (auto &BB : F) {
    std::vector<LoadInst *> Loads;
    std::vector<StoreInst *> Stores;
    // Find packable instructions
    auto MM = std::make_unique<MatchManager>(SupportedInsts, BB);
    for (auto &I : BB) {
      if (auto *LI = dyn_cast<LoadInst>(&I)) {
        if (LI->isSimple())
          Loads.push_back(LI);
      } else if (auto *SI = dyn_cast<StoreInst>(&I)) {
        if (SI->isSimple())
          Stores.push_back(SI);
      }
    }

    auto VPCtx = std::make_unique<VectorPackContext>(&BB);
    auto LoadDAG = std::make_unique<ConsecutiveAccessDAG>();
    auto StoreDAG = std::make_unique<ConsecutiveAccessDAG>();
    buildAccessDAG<LoadInst>(*LoadDAG, Loads, DL, SE);
    buildAccessDAG<StoreInst>(*StoreDAG, Stores, DL, SE);

    LoadInfo[&BB] = std::make_unique<AccessLayoutInfo>(*LoadDAG);
    StoreInfo[&BB] = std::make_unique<AccessLayoutInfo>(*StoreDAG);

    MMs[&BB] = std::move(MM);
    LDAs[&BB] = std::make_unique<LocalDependenceAnalysis>(AA, &BB, VPCtx.get());
    VPCtxs[&BB] = std::move(VPCtx);
    LoadDAGs[&BB] = std::move(LoadDAG);
    StoreDAGs[&BB] = std::move(StoreDAG);
  }
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

extern VectorPack *findExtendingLoadPack(const OperandPack &OP, BasicBlock *BB,
                                         Packer *Pkr);

const OperandProducerInfo Packer::getProducerInfo(const VectorPackContext *VPCtx, const OperandPack *OP) {
#if 0
#if 1
  bool Inserted;
  decltype(Producers)::iterator It;
  std::tie(It, Inserted) = Producers.try_emplace(OP);
  if (!Inserted)
    return It->second;
  
  OperandProducerInfo &OPI = It->second;
#else
  if (Producers.count(OP))
    return Producers[OP];
  auto &OPI = Producers[OP];
#endif
#endif
  if (OP->OPIValid)
    return OP->OPI;
  OP->OPIValid = true;
  auto &OPI = OP->OPI;

  auto *BB = VPCtx->getBasicBlock();
  auto &LDA = *LDAs[BB];
  auto &MM = *MMs[BB];

  unsigned NumLanes = OP->size();
  BitVector Elements(VPCtx->getNumValues());
  BitVector Depended(VPCtx->getNumValues());
  OPI.Feasible = true;
  bool AllLoads = true;
  bool HasUndef = false;
  for (unsigned i = 0; i < NumLanes; i++) {
    auto *V = (*OP)[i];
    if (!V) {
      HasUndef = true;
      continue;
    }
    auto *I = dyn_cast<Instruction>(V);
    if (!I) {
      AllLoads = false;
      continue;
    }

    if (!isa<LoadInst>(I))
      AllLoads = false;

    if (!I || I->getParent() != BB)
      OPI.Feasible = false;

    unsigned InstId = VPCtx->getScalarId(I);
    if (!checkIndependence(LDA, *VPCtx, I, Elements, Depended))
      OPI.Feasible = false;
    Elements.set(InstId);
    Depended |= LDA.getDepended(I);
  }

  OPI.Elements = std::move(Elements);

  if (!OPI.Feasible)
    return OPI;

  if (AllLoads) {
    if (auto *LoadVP = findExtendingLoadPack(*OP, BB, this))
      OPI.LoadProducer = LoadVP;
    return OPI;
  }

  if (HasUndef) {
    OPI.Feasible = false;
    return OPI;
  }

  for (auto *Inst : getInsts()) {
    ArrayRef<BoundOperation> LaneOps = Inst->getLaneOps();
    if (LaneOps.size() != NumLanes)
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
      OPI.Producers.push_back(
          VPCtx->createVectorPack(Lanes, OPI.Elements, Depended, Inst, TTI));
    }
  }
  OPI.Feasible = !OPI.Producers.empty();
  return OPI;
}

//ArrayRef<VectorPack *>
//Packer::findExtensionsForOperand(VectorPackContext *VPCtx,
//                                 const OperandPack *OP, BitVector Elements,
//                                 BitVector Depended) {
//  auto *BB = VPCtx->getBasicBlock();
//  auto &MM = *MMs[BB];
//  auto &Cache = *ExtensionCaches[BB];
//  auto It = Cache.find(OP);
//  if (It != Cache.end()) {
//    return It->second;
//  }
//
//  unsigned NumLanes = OP->size();
//  auto &Extensions = Cache[OP];
//
//  for (auto *Inst : SupportedInsts) {
//    ArrayRef<BoundOperation> LaneOps = Inst->getLaneOps();
//    if (LaneOps.size() != NumLanes)
//      continue;
//
//    std::vector<const Operation::Match *> Lanes;
//    for (unsigned i = 0; i < NumLanes; i++) {
//      ArrayRef<Operation::Match> Matches =
//          MM.getMatchesForOutput(LaneOps[i].getOperation(), (*OP)[i]);
//      if (Matches.empty())
//        break;
//      // FIXME: consider multiple matches for the same operation
//      Lanes.push_back(&Matches[0]);
//    }
//
//    if (Lanes.size() == NumLanes) {
//      Extensions.push_back(
//          VPCtx->createVectorPack(Lanes, Elements, Depended, Inst, TTI));
//    }
//  }
//  return Extensions;
//}
