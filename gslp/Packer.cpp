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
    ExtensionCaches[&BB] = std::make_unique<ExtensionCache>();
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

ArrayRef<VectorPack *> Packer::findExtensions(VectorPackContext *VPCtx,
                                              const OperandPack *OP,
                                              BitVector Elements,
                                              BitVector Depended) {
  auto *BB = VPCtx->getBasicBlock();
  auto &MM = *MMs[BB];
  auto &Cache = *ExtensionCaches[BB];
  auto It = Cache.find(OP);
  if (It != Cache.end()) {
    return It->second;
  }

  unsigned NumLanes = OP->size();
  auto &Extensions = Cache[OP];

  for (auto *Inst : SupportedInsts) {
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
      Extensions.push_back(
          VPCtx->createVectorPack(Lanes, Elements, Depended, Inst, TTI));
    }
  }
  return Extensions;
}
