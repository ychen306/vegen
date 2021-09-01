#include "Packer.h"
#include "MatchManager.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"

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

// Util class to order basic block in reverse post order
class BlockOrdering {
  DenseMap<BasicBlock *, unsigned> Order;

public:
  BlockOrdering(Function *F) {
    ReversePostOrderTraversal<Function *> RPO(F);
    unsigned i = 0;
    for (BasicBlock *BB : RPO)
      Order[BB] = i++;
  }

  bool comesBefore(BasicBlock *BB1, BasicBlock *BB2) const {
    assert(Order.count(BB1) && Order.count(BB2));
    return Order.lookup(BB1) < Order.lookup(BB2);
  }
};

class AddRecLoopRewriter : public SCEVRewriteVisitor<AddRecLoopRewriter> {
public:
  using LoopToLoopMap = DenseMap<const Loop *, const Loop *>;

private:
  const LoopToLoopMap &Loops;

public:
  AddRecLoopRewriter(ScalarEvolution &SE, const LoopToLoopMap &Loops)
      : SCEVRewriteVisitor<AddRecLoopRewriter>(SE), Loops(Loops) {}

  static const SCEV *rewrite(ScalarEvolution &SE, const SCEV *Expr,
                             const LoopToLoopMap &Loops) {
    AddRecLoopRewriter Rewriter(SE, Loops);
    return Rewriter.visit(Expr);
  }

  const SCEV *visitAddRecExpr(const SCEVAddRecExpr *Expr) {
    SmallVector<const SCEV *> Operands;
    for (auto *Op : Expr->operands())
      Operands.push_back(visit(Op));
    auto *OldLoop = Expr->getLoop();
    auto *NewLoop = Loops.lookup(OldLoop);
    return SE.getAddRecExpr(Operands, NewLoop ? NewLoop : OldLoop,
                            Expr->getNoWrapFlags());
  }
};

} // end anonymous namespace

static SmallVector<const Loop *, 4> getLoopNest(LoopInfo &LI, Instruction *I) {
  SmallVector<const Loop *, 4> LoopNest;
  for (auto *L = LI.getLoopFor(I->getParent()); L; L = L->getParentLoop())
    LoopNest.push_back(L);
  return LoopNest;
}

/// Take the address space operand from the Load/Store instruction.
/// Returns -1 if this is not a valid Load/Store instruction.
static unsigned getAddressSpaceOperand(Value *I) {
  if (LoadInst *L = dyn_cast<LoadInst>(I))
    return L->getPointerAddressSpace();
  if (StoreInst *S = dyn_cast<StoreInst>(I))
    return S->getPointerAddressSpace();
  return -1;
}

// llvm::isConsecutiveAccess modified to work for when A and B are in two
// separate loop nest
static bool isConsecutive(Instruction *A, Instruction *B, const DataLayout &DL,
                          ScalarEvolution &SE, LoopInfo &LI) {
  auto LoopNest1 = getLoopNest(LI, A);
  auto LoopNest2 = getLoopNest(LI, B);
  if (LoopNest1.size() != LoopNest2.size())
    return false;

  const Loop *L1, *L2;
  AddRecLoopRewriter::LoopToLoopMap Loops;
  for (const auto &Pair : zip(LoopNest1, LoopNest2)) {
    std::tie(L1, L2) = Pair;
    if (SE.getBackedgeTakenCount(L1) != SE.getBackedgeTakenCount(L2))
      return false;
    Loops[L2] = L1;
  }

  Value *PtrA = getLoadStorePointerOperand(A);
  Value *PtrB = getLoadStorePointerOperand(B);
  unsigned ASA = getAddressSpaceOperand(A);
  unsigned ASB = getAddressSpaceOperand(B);

  // Check that the address spaces match and that the pointers are valid.
  if (!PtrA || !PtrB || (ASA != ASB))
    return false;

  // Make sure that A and B are different pointers.
  if (PtrA == PtrB)
    return false;

  unsigned IdxWidth = DL.getIndexSizeInBits(ASA);
  Type *Ty = cast<PointerType>(PtrA->getType())->getElementType();

  APInt OffsetA(IdxWidth, 0), OffsetB(IdxWidth, 0);
  PtrA = PtrA->stripAndAccumulateInBoundsConstantOffsets(DL, OffsetA);
  PtrB = PtrB->stripAndAccumulateInBoundsConstantOffsets(DL, OffsetB);

  // Retrieve the address space again as pointer stripping now tracks through
  // `addrspacecast`.
  ASA = cast<PointerType>(PtrA->getType())->getAddressSpace();
  ASB = cast<PointerType>(PtrB->getType())->getAddressSpace();
  // Check that the address spaces match and that the pointers are valid.
  if (ASA != ASB)
    return false;

  IdxWidth = DL.getIndexSizeInBits(ASA);
  OffsetA = OffsetA.sextOrTrunc(IdxWidth);
  OffsetB = OffsetB.sextOrTrunc(IdxWidth);

  APInt Size(IdxWidth, DL.getTypeStoreSize(Ty));

  //  OffsetDelta = OffsetB - OffsetA;
  const SCEV *OffsetSCEVA = SE.getConstant(OffsetA);
  const SCEV *OffsetSCEVB = SE.getConstant(OffsetB);
  const SCEV *OffsetDeltaSCEV = SE.getMinusSCEV(OffsetSCEVB, OffsetSCEVA);
  const APInt &OffsetDelta = cast<SCEVConstant>(OffsetDeltaSCEV)->getAPInt();

  // Check if they are based on the same pointer. That makes the offsets
  // sufficient.
  if (PtrA == PtrB)
    return OffsetDelta == Size;

  // Compute the necessary base pointer delta to have the necessary final delta
  // equal to the size.
  // BaseDelta = Size - OffsetDelta;
  const SCEV *SizeSCEV = SE.getConstant(Size);
  const SCEV *BaseDelta = SE.getMinusSCEV(SizeSCEV, OffsetDeltaSCEV);

  // Otherwise compute the distance with SCEV between the base pointers.
  const SCEV *PtrSCEVA = SE.getSCEV(PtrA);
  const SCEV *PtrSCEVB =
      AddRecLoopRewriter::rewrite(SE, SE.getSCEV(PtrB), Loops);
  const SCEV *X = SE.getAddExpr(PtrSCEVA, BaseDelta);
  return X == PtrSCEVB;
}

Packer::Packer(ArrayRef<const InstBinding *> Insts, Function &F,
               AliasAnalysis *AA, const DataLayout *DL, LoopInfo *LI,
               ScalarEvolution *SE, DominatorTree *DT, PostDominatorTree *PDT,
               DependenceInfo *DI, LazyValueInfo *LVI, TargetTransformInfo *TTI,
               BlockFrequencyInfo *BFI)
    : F(&F), VPCtx(&F), DA(*AA, *SE, *DT, &F, LVI, &VPCtx), MM(Insts, F),
      SupportedInsts(Insts.vec()), TTI(TTI), BFI(BFI) {

  // Setup analyses and determine search space
  for (auto &BB : F) {
    std::vector<LoadInst *> Loads;
    std::vector<StoreInst *> Stores;

    // Find packable instructions
    for (auto &I : BB) {
      if (auto *LI = dyn_cast<LoadInst>(&I)) {
        if (LI->isSimple())
          Loads.push_back(LI);
      } else if (auto *SI = dyn_cast<StoreInst>(&I)) {
        if (SI->isSimple())
          Stores.push_back(SI);
      }
    }

    auto LoadDAG = std::make_unique<ConsecutiveAccessDAG>();
    auto StoreDAG = std::make_unique<ConsecutiveAccessDAG>();
    buildAccessDAG<LoadInst>(*LoadDAG, Loads, DL, SE);
    buildAccessDAG<StoreInst>(*StoreDAG, Stores, DL, SE);

    LoadInfo[&BB] = std::make_unique<AccessLayoutInfo>(*LoadDAG);
    StoreInfo[&BB] = std::make_unique<AccessLayoutInfo>(*StoreDAG);

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

// Assuming all elements of `OP` are loads, try to find an extending load pack.
static void findExtendingLoadPacks(const OperandPack &OP, BasicBlock *BB,
                                   Packer *Pkr,
                                   SmallVectorImpl<VectorPack *> &Extensions) {
  auto *VPCtx = Pkr->getContext();
  auto &LoadDAG = Pkr->getLoadDAG(BB);
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
          VPCtx->createLoadPack(Loads, Elements, Depended, Pkr->getTTI()));
      return;
    }
  }
}

const OperandProducerInfo &Packer::getProducerInfo(BasicBlock *BB,
                                                   const OperandPack *OP) {
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

    if (!I || I->getParent() != BB) {
      OPI.Feasible = false;
      continue;
    }

    unsigned InstId = VPCtx.getScalarId(I);
    if (!checkIndependence(DA, VPCtx, I, Elements, Depended))
      OPI.Feasible = false;
    Elements.set(InstId);
    Depended |= DA.getDepended(I);
  }

  OPI.Elements = std::move(Elements);

  if (!OPI.Feasible || OPI.Elements.count() < 2)
    return OPI;

  if (AllLoads) {
    findExtendingLoadPacks(*OP, BB, this, OPI.LoadProducers);
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
  if (isa<GetElementPtrInst>(I))
    return 0;
  if (isa<PHINode>(I) || isa<CallInst>(I) || isa<ReturnInst>(I) ||
      I->isTerminator() || isa<AllocaInst>(I))
    return 1;
  SmallVector<const Value *, 4> Operands(I->operand_values());
  return TTI->getArithmeticInstrCost(
      I->getOpcode(), I->getType(), TTI::TCK_RecipThroughput, TTI::OK_AnyValue,
      TTI::OK_AnyValue, TTI::OP_None, TTI::OP_None, Operands, I);
}

BasicBlock *Packer::getBlockForOperand(const OperandPack *OP) const {
  BasicBlock *BB = nullptr;
  for (auto *V : *OP) {
    auto *I = dyn_cast_or_null<Instruction>(V);
    if (!I)
      continue;

    if (!BB) {
      BB = I->getParent();
      continue;
    }

    // Can't produce OP within a single basic block
    if (BB != I->getParent())
      return nullptr;
  }
  return BB;
}
