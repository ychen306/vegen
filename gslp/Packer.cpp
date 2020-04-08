#include "Packer.h"
#include "MatchManager.h"

using namespace llvm;

Packer::Packer(ArrayRef<InstBinding *> SupportedInsts, llvm::Function &F,
               AliasAnalysis *AA, const DataLayout *DL, ScalarEvolution *SE,
               TargetTransformInfo *TTI, BlockFrequencyInfo *BFI)
    : SupportedInsts(SupportedInsts.vec()), TTI(TTI), BFI(BFI), Index(F) {
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

    MMs[&BB] = std::move(MM);
    LDAs[&BB] = std::make_unique<LocalDependenceAnalysis>(AA, &BB, VPCtx.get());
    VPCtxs[&BB] = std::move(VPCtx);
    LoadDAGs[&BB] = std::move(LoadDAG);
    StoreDAGs[&BB] = std::move(StoreDAG);
  }

  VectorPackSet TempPacks(&F);
  for (auto *Inst : SupportedInsts) {
    for (auto &BB : F) {
      InstBindings[&BB].insert(Inst);
    }
  }
}

void Packer::findExtensionForOnePack(const VectorPack &VP,
                                     const VectorPackSet &Packs,
                                     std::vector<VectorPack *> &Extensions) {
  for (auto &OpndPack : VP.getOperandPacks()) {
    // Figure out where the scalar operands are produced.
    // Bail if they are produced in different basic blocks.
    BasicBlock *BB = nullptr;
    bool FromSingleBB = true;
    for (auto *V : OpndPack) {
      auto *I = dyn_cast<Instruction>(V);
      if (!I)
        continue;
      if (!BB)
        BB = I->getParent();
      else if (I->getParent() != BB) {
        FromSingleBB = false;
        break;
      }
    }
    // Can't extend from this operand pack
    if (!FromSingleBB || !BB)
      break;

    extendWithDef(OpndPack, Packs, Extensions, LoadDAGs, MMs, VPCtxs, LDAs,
                  InstBindings, TTI);
  }
}

// FIXME: remove Insts and take the list of all supported instruction instead
// FIXME: ignore lane order here.
// Find vector packs that produces operand pack
void extendWithDef(
    const VectorPack::OperandPack &OpndPack, const VectorPackSet &ExistingPacks,
    std::vector<VectorPack *> &Extensions,
    DenseMap<BasicBlock *, std::unique_ptr<ConsecutiveAccessDAG>> &LoadDAGs,
    DenseMap<BasicBlock *, std::unique_ptr<MatchManager>> &MMs,
    DenseMap<BasicBlock *, std::unique_ptr<VectorPackContext>> &VPCtxs,
    DenseMap<BasicBlock *, std::unique_ptr<LocalDependenceAnalysis>> &LDAs,
    DenseMap<BasicBlock *, SmallPtrSet<const InstBinding *, 4>> &Insts,
    TargetTransformInfo *TTI) {
  BitVector Elements;
  BitVector Depended;

  BasicBlock *BB = nullptr;

  VectorPackContext *VPCtx = nullptr;
  MatchManager *MM = nullptr;
  ConsecutiveAccessDAG *LoadDAG = nullptr;

  // First, check if the operand pack is indepdendent.
  // We can't extend if it's not independent.
  for (Value *V : OpndPack) {
    // Also bail if we can't produce this pack at current basic block
    auto *I = dyn_cast<Instruction>(V);
    if (!I)
      return;
    if (!BB) {
      BB = I->getParent();

      VPCtx = VPCtxs[BB].get();
      MM = MMs[BB].get();
      LoadDAG = LoadDAGs[BB].get();

      Elements = BitVector(VPCtx->getNumValues());
      Depended = BitVector(VPCtx->getNumValues());
    } else if (I->getParent() != BB)
      return;

    assert(VPCtx);

    // Check dependence
    unsigned ValueId = VPCtx->getScalarId(I);
    if (Elements.test(ValueId))
      return;

    BitVector Depended2 = LDAs[BB]->getDepended(I);
    if (Depended.test(ValueId))
      return;
    if (Depended2.anyCommon(Elements))
      return;

    Elements.set(ValueId);
    Depended |= Depended2;
  }

  if (auto LoadsOrNull = castOperandPack<LoadInst>(OpndPack)) {
    std::vector<LoadInst *> Loads;
    SmallPtrSet<LoadInst *, 4> LoadSet(LoadsOrNull->begin(),
                                       LoadsOrNull->end());
    for (auto *LI : LoadsOrNull.getValue()) {
      SmallPtrSet<LoadInst *, 4> LoadsRemained = LoadSet;
      // See if there's a proper ordering of these loads starting from `LI`,
      // so that they are consecutive.
      LoadsRemained.erase(LI);
      LoadInst *CurLoad = LI;
      Loads = {LI};
      while (!LoadsRemained.empty()) {
        auto It = LoadDAG->find(CurLoad);
        if (It == LoadDAG->end())
          break;
        LoadInst *NextLoad = nullptr;
        for (auto *I : It->second) {
          auto *LI = cast<LoadInst>(I);
          if (LoadsRemained.erase(LI)) {
            NextLoad = LI;
            break;
          }
        }
        if (!NextLoad)
          break;
        Loads.push_back(NextLoad);
        CurLoad = NextLoad;
      }
      if (Loads.size() == LoadSet.size())
        break;
    }
    if (Loads.size() != LoadSet.size())
      return;
    Extensions.push_back(VPCtx->createLoadPack(Loads, Elements, Depended, TTI));
    return;
  }

  if (auto PHIsOrNull = castOperandPack<PHINode>(OpndPack)) {
    Extensions.push_back(VPCtx->createPhiPack(PHIsOrNull.getValue(), TTI));
    return;
  }

  // NOTE: We can't extend with Store packs vector stores don't produce
  // anything...

  // Aux func to enumerate cross product of `LaneMatches`
  auto EnumeratePacks =
      [&](const InstBinding *Inst,
          const std::vector<ArrayRef<Operation::Match>> &LaneMatches) {
        assert(Inst->getLaneOps().size() == LaneMatches.size());
        unsigned N = 1;
        for (auto &Matches : LaneMatches)
          N *= Matches.size();
        for (unsigned i = 0; i < N; i++) {
          // `i` represent a particular member of the cross product.
          // Decode `i` here.
          unsigned Encoded = i;
          std::vector<const Operation::Match *> Lanes;
          for (auto &Matches : LaneMatches) {
            unsigned M = Matches.size();
            Lanes.push_back(&Matches[Encoded % M]);
            Encoded /= M;
          }

          Extensions.push_back(
              VPCtx->createVectorPack(Lanes, Elements, Depended, Inst, TTI));
        }
      };
  std::vector<ArrayRef<Operation::Match>> LaneMatches;
  for (auto *Inst : Insts[BB]) {
    // See if we can pack with this Inst
    ArrayRef<BoundOperation> LaneOps = Inst->getLaneOps();
    unsigned NumLanes = LaneOps.size();
    if (NumLanes != OpndPack.size())
      continue;
    LaneMatches.resize(NumLanes);
    bool Feasible = true;
    unsigned LaneId = 0;
    for (const auto &LaneOp : LaneOps) {
      ArrayRef<Operation::Match> Matches =
          MM->getMatchesForOutput(LaneOp.getOperation(), OpndPack[LaneId]);
      if (Matches.empty()) {
        Feasible = false;
        break;
      }
      LaneMatches[LaneId] = Matches;
      LaneId++;
    }
    if (Feasible)
      EnumeratePacks(Inst, LaneMatches);
  }
}

float Packer::evalSeedPacks(const VectorPackSet &Packs, unsigned Alpha) {
  unsigned NumTrials = Alpha * Packs.getNumPacks();
  float BestCost = Packs.getCostSaving(TTI, BFI);
  std::vector<VectorPack *> Extensions;
  for (unsigned i = 0; i < NumTrials; i++) {
    VectorPackSet ScratchPacks = Packs;
    bool Changed;
    unsigned FirstUnprocessedPackId = 0;
    do {
      Changed = false;
      Extensions.clear();
      for (unsigned i = FirstUnprocessedPackId; i < ScratchPacks.getNumPacks();
           i++)
        findExtensionForOnePack(ScratchPacks.getPack(i), ScratchPacks,
                                Extensions);
      FirstUnprocessedPackId = ScratchPacks.getNumPacks() - 1;
      random_shuffle(Extensions.begin(), Extensions.end(), rand_int);
      for (auto *VP : Extensions)
        Changed |= ScratchPacks.tryAdd(VP);
    } while (Changed);
    float Cost = ScratchPacks.getCostSaving(TTI, BFI);
    if (Cost < BestCost) {
      BestCost = Cost;
    }
  }
  return BestCost;
};
