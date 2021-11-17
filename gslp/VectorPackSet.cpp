#include "VectorPackSet.h"
#include "BlockBuilder.h"
#include "ControlDependence.h"
#include "Packer.h"
#include "llvm/ADT/EquivalenceClasses.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Transforms/Utils/PromoteMemToReg.h"

using namespace llvm;
using namespace PatternMatch;

static cl::opt<bool> RescheduleScalars(
    "reschedule-scalar",
    cl::desc(
        "run VectorPackSet::codegen and reschdule even when not vectorizing"),
    cl::init(false));

static cl::opt<bool> DumpAfterErasingOldBlocks("dump-after-erasing-old-blocks",
                                               cl::init(false));

static cl::opt<bool>
    DumpBeforeErasingOldBlocks("dump-before-erasing-old-blocks",
                               cl::init(false));

static bool shouldSkip(const VectorPack *VP) {
  return false;
  //return VP->getProducer() && VP->getProducer()->getName().contains("builtin");
}

namespace {

class VectorCodeGen {
  Packer &Pkr;
  const VectorPackContext *VPCtx;
  Function *F;
  BasicBlock *Entry;
  IntrinsicBuilder &Builder;
  const DenseMap<Value *, const VectorPack *> &ValueToPackMap;

  DenseMap<const llvm::Value *, VectorPackIndex> ValueIndex;
  PackToValueTy MaterializedPacks;
  DenseMap<const ConditionPack *, Value *> MaterializedCondPacks;
  // Instead of moving PHIs around,
  // we will demote them and implement control-flow join through memory
  DenseMap<PHINode *, Value *> ReplacedPHIs;
  // Track the last used block for a given condition,
  // these are the blocks where we will store the incoming values to the demoted
  // allocas.
  SmallVector<AllocaInst *> Allocas;
  DenseMap<Value *, Value *> ReplacedUses;

  Value *gatherOperandPack(const OperandPack &OP);
  Value *getOrEmitConditionPack(const ConditionPack *CP);
  Value *getMaskForInsts(
      ArrayRef<Value *>,
      const DenseMap<VLoop *, const ControlCondition *> *LoopActiveConds);

  // Ok, this is bad.
  DenseMap<VLoop *, Value *> ShouldEnterLoop;
  DenseMap<VLoop *, Value *> ShouldEnterLoopVec;

  bool shouldVectorizeActiveConds(VLoop *VL) const;

  // Lower a vloop and return the loop-header and exit.
  std::pair<BasicBlock *, BasicBlock *>
  emitLoop(VLoop &VL, BasicBlock *Preheader = nullptr);

  Value *useScalar(Value *V) {
    if (ReplacedUses.count(V))
      return ReplacedUses.lookup(V);
    if (auto *Demoted = ReplacedPHIs.lookup(dyn_cast<PHINode>(V)))
      return Demoted;
    if (ValueToPackMap.lookup(V)) {
      if (shouldSkip(ValueToPackMap.lookup(V)))
        return V;
      assert(ValueIndex.count(V));
      return ValueIndex[V].Extracted;
    }
    return V;
  }

public:
  VectorCodeGen(Packer &Pkr, IntrinsicBuilder &Builder,
                const DenseMap<Value *, const VectorPack *> &ValueToPackMap)
      : Pkr(Pkr), VPCtx(Pkr.getContext()), F(Pkr.getFunction()), Entry(nullptr),
        Builder(Builder), ValueToPackMap(ValueToPackMap) {}

  void run();
};
} // namespace

bool VectorCodeGen::shouldVectorizeActiveConds(VLoop *VL) const {
  for (auto *CoVL : Pkr.getVLoopInfo().getCoIteratingLoops(VL)) {
    auto *And = dyn_cast<ConditionAnd>(CoVL->getBackEdgeCond());
    if (And && ValueToPackMap.count(And->Cond))
      return true;
  }
  return false;
}

static void setInsertAtEndOfBlock(IRBuilderBase &Builder, BasicBlock *BB) {
  if (auto *Terminator = BB->getTerminator())
    Builder.SetInsertPoint(Terminator);
  else
    Builder.SetInsertPoint(BB);
}

static const VLoop *getVLoop(Packer &Pkr, BasicBlock *BB) {
  auto &LI = Pkr.getLoopInfo();
  auto *L = LI.getLoopFor(BB);
  assert(L);
  auto &VLI = Pkr.getVLoopInfo();
  auto *VL = VLI.getVLoop(L);
  assert(VL);
  return VL;
}

static const ControlCondition *getLoopCondAux(
    Packer &Pkr, VLoop *VL,
    const DenseMap<VLoop *, const ControlCondition *> *LoopActiveConds) {
  auto *C = VL->getLoopCond();
  auto *ParentVL = VL->getParent();
  if (!LoopActiveConds || !ParentVL)
    return C;
  return Pkr.getCDA().concat(LoopActiveConds->lookup(ParentVL), C);
}

static const ControlCondition *getBlockConditionAux(
    Packer &Pkr, BasicBlock *BB,
    const DenseMap<VLoop *, const ControlCondition *> *LoopActiveConds) {
  auto *C = Pkr.getBlockCondition(BB);
  if (!LoopActiveConds)
    return C;
  auto *VL = getVLoop(Pkr, BB);
  return Pkr.getCDA().concat(LoopActiveConds->lookup(VL), C);
}

static const ControlCondition *getEdgeCondAux(
    Packer &Pkr, BasicBlock *Src, BasicBlock *Dst,
    const DenseMap<VLoop *, const ControlCondition *> *LoopActiveConds) {
  auto *C = Pkr.getEdgeCondition(Src, Dst);
  if (!LoopActiveConds)
    return C;

  auto *VL = getVLoop(Pkr, Src);
  if (VL != getVLoop(Pkr, Dst))
    return C;

  return Pkr.getCDA().concat(LoopActiveConds->lookup(VL), C);
}

Value *VectorCodeGen::getMaskForInsts(
    ArrayRef<Value *> Vals,
    const DenseMap<VLoop *, const ControlCondition *> *LoopActiveConds =
        nullptr) {
  SmallVector<const ControlCondition *> Conds;
  auto *SomeVal = *find_if(Vals, [](Value *V) { return V; });
  auto *C = getBlockConditionAux(Pkr, cast<Instruction>(SomeVal)->getParent(),
                                 LoopActiveConds);
  for (auto *V : Vals)
    Conds.push_back(V ? getBlockConditionAux(Pkr,
                                             cast<Instruction>(V)->getParent(),
                                             LoopActiveConds)
                      : C);
  auto *CP = VPCtx->getConditionPack(Conds);
  // nullptr means it's all true
  if (!CP)
    return nullptr;
  return getOrEmitConditionPack(CP);
};

// Get the vector value representing `OP'.
// If `OP` is not directly produced by another Pack,
// we need to emit code to either swizzle it together.
Value *VectorCodeGen::gatherOperandPack(const OperandPack &OP) {
  struct GatherEdge {
    unsigned SrcIndex;
    unsigned DestIndex;
  };

  DenseMap<const VectorPack *, SmallVector<GatherEdge, 4>> SrcPacks;
  DenseMap<Value *, SmallVector<unsigned, 4>> SrcScalars;

  // Figure out sources of the values in `OP`
  const unsigned NumValues = OP.size();
  for (unsigned i = 0; i < NumValues; i++) {
    auto *V = OP[i];
    // Null means don't care/undef
    if (!V)
      continue;
    auto It = ValueIndex.find(V);
    if (It != ValueIndex.end()) {
      // V is produced by a pack
      auto &VPIdx = It->second;
      // Remember we need to gather from this vector to the `i`th element
      SrcPacks[VPIdx.VP].push_back({VPIdx.Idx, i});
    } else {
      // Remember that we need to insert `V` as the `i`th element
      SrcScalars[useScalar(V)].push_back(i);
    }
  }

  using ShuffleMaskTy = SmallVector<Constant *, 8>;
  ShuffleMaskTy Undefs(NumValues);
  auto *Int32Ty = Type::getInt32Ty(Builder.getContext());
  auto *UndefInt32 = UndefValue::get(Int32Ty);
  for (auto &U : Undefs)
    U = UndefInt32;

  // Here's the codegen strategy we will use.
  //
  // Suppose we need to gather from N vectors,
  // and the output vector has M elements.
  // We then generate N partial gather, resulting in N vector if size M
  // Then we merge these temporaries to get the final vector.
  //
  // Additionally, if any of the source values come from scalars, we just insert
  // them.
  //
  // We don't care about the performance that much at this stage
  // because we are going to optimize the gather sequences later.

  // 1) Emit the partial gathers
  struct PartialGather {
    BitVector DefinedBits;
    Value *Gather;
  };
  std::vector<PartialGather> PartialGathers;

  for (auto &KV : SrcPacks) {
    auto *SrcVP = KV.first;
    auto &GatherEdges = KV.second;

    BitVector DefinedBits(NumValues);
    // Figure out which values we want to gather
    ShuffleMaskTy MaskValues = Undefs;
    for (auto &GE : GatherEdges) {
      assert(GE.DestIndex < MaskValues.size());
      MaskValues[GE.DestIndex] = ConstantInt::get(Int32Ty, GE.SrcIndex);
      DefinedBits.set(GE.DestIndex);
    }

    auto *Src = MaterializedPacks.lookup(SrcVP);
    assert(Src);
    auto *Mask = ConstantVector::get(MaskValues);
    Value *Gather;
    // Minor optimization: avoid unnecessary shuffle.
    if (SrcVP->getOrderedValues().size() == NumValues &&
        ShuffleVectorInst::isIdentityMask(Mask))
      Gather = Src;
    else
      Gather = Builder.CreateShuffleVector(Src, UndefValue::get(Src->getType()),
                                           Mask);

    PartialGathers.push_back({DefinedBits, Gather});
  }

  Value *Acc = nullptr;
  if (!PartialGathers.empty()) {
    // 2) Merge the partial gathers
    BitVector DefinedBits = PartialGathers.front().DefinedBits;
    Acc = PartialGathers.front().Gather;
    for (auto &PG : drop_begin(PartialGathers)) {
      ShuffleMaskTy Mask = Undefs;
      assert(Mask.size() == NumValues);
      // Select from Acc
      for (unsigned Idx : DefinedBits.set_bits())
        Mask[Idx] = ConstantInt::get(Int32Ty, Idx);
      // Select from the partial gather
      for (unsigned Idx : PG.DefinedBits.set_bits())
        Mask[Idx] = ConstantInt::get(Int32Ty, NumValues + Idx);
      Acc = Builder.CreateShuffleVector(Acc, PG.Gather,
                                        ConstantVector::get(Mask));

      assert(!DefinedBits.anyCommon(PG.DefinedBits));
      DefinedBits |= PG.DefinedBits;
    }
  } else {
    auto *VecTy = getVectorType(OP);
    Acc = UndefValue::get(VecTy);
  }

  // 3) Insert the scalar values
  for (auto &KV : SrcScalars) {
    Value *V = KV.first;
    auto &Indices = KV.second;
    for (unsigned Idx : Indices) {
      Acc = Builder.CreateInsertElement(Acc, V, Idx, "gslp.insert");
    }
  }

  assert(Acc);
  return Acc;
}

Value *VectorCodeGen::getOrEmitConditionPack(const ConditionPack *CP) {
  assert(CP);
  if (auto *V = MaterializedCondPacks.lookup(CP))
    return V;

  if (CP->Kind == ConditionPack::CP_And) {
    assert(CP->OP);
    Value *Cond = gatherOperandPack(*CP->OP);
    if (CP->ElemsToFlip.count()) {
      SmallVector<Constant *, 8> Mask;
      auto &Ctx = Builder.getContext();
      Mask.resize(CP->Conds.size(), ConstantInt::getFalse(Ctx));
      for (unsigned i : CP->ElemsToFlip.set_bits())
        Mask[i] = ConstantInt::getTrue(Ctx);
      Cond = Builder.CreateXor(Cond, ConstantVector::get(Mask));
    }
    if (!CP->Parent)
      return Cond;
    auto *ParentCond = getOrEmitConditionPack(CP->Parent);
    return Builder.CreateAnd(ParentCond, Cond);
  }

  llvm_unreachable("OR pack not supported");
}

void VectorPackSet::add(const VectorPack *VP) {
  PackedValues |= VP->getElements();
  AllPacks.push_back(VP);

  for (Value *V : VP->elementValues())
    ValueToPackMap[V] = VP;
}

bool VectorPackSet::isCompatibleWith(const VectorPack &VP) const {
  // Abort if one of the value we want to produce is produced by another pack
  if (PackedValues.anyCommon(VP.getElements())) {
    return false;
  }

  SmallPtrSet<Value *, 8> NewValues;
  for (auto *V : VP.elementValues())
    NewValues.insert(V);

  // Do a DFS on the dependence graph starting from VP.
  // We want to see if we can get back to any of VP's values
  SmallVector<const VectorPack *> Worklist{&VP};
  DenseSet<const VectorPack *> Visited;
  while (!Worklist.empty()) {
    auto *VP = Worklist.pop_back_val();

    bool Inserted = Visited.insert(VP).second;
    if (!Inserted)
      continue;

    for (auto *V : VP->dependedValues()) {
      if (NewValues.count(V))
        return false;
      auto It = ValueToPackMap.find(V);
      if (It == ValueToPackMap.end())
        continue;
      Worklist.push_back(It->second);
    }
  }

  return true;
}

bool VectorPackSet::tryAdd(const VectorPack *VP) {
  if (!isCompatibleWith(*VP))
    return false;
  add(VP);
  return true;
}

// mapping a nested loop to the *sub loop of VL* that contains it
static void fillSubLoopMap(VLoop &VL, DenseMap<VLoop *, VLoop *> &SubLoopMap) {
  for (auto &SubVL : VL.getSubLoops()) {
    SubLoopMap[SubVL.get()] = SubVL.get();
    SmallVector<VLoop *> Worklist{SubVL.get()};
    while (!Worklist.empty()) {
      for (auto &SubSubVL : Worklist.pop_back_val()->getSubLoops()) {
        SubLoopMap[SubSubVL.get()] = SubVL.get();
        Worklist.push_back(SubSubVL.get());
      }
    }
  }
}

// Topsort the instructions s.t. instructions in the same packs are grouped
// together.
static std::vector<PointerUnion<Instruction *, VLoop *>>
schedule(VLoop &VL, const DenseMap<Value *, const VectorPack *> &ValueToPackMap,
         Packer &Pkr) {
  auto &DA = Pkr.getDA();
  auto &VLI = Pkr.getVLoopInfo();
  assert(!VL.isLoop() || VLI.getCoIteratingLeader(&VL) == &VL);

  // Schedule the instruction to the pack dependence.
  // In particular, we want the instructions to be packed stay together.
  const VectorPackContext *VPCtx = Pkr.getContext();
  using SchedulerItem = PointerUnion<Instruction *, const VectorPack *,
                                     const ControlCondition *, VLoop *>;
  DenseSet<void *> Reordered;
  std::vector<PointerUnion<Instruction *, VLoop *>> ScheduledItems;

  DenseMap<VLoop *, VLoop *> SubLoopMap;
  if (VL.isLoop()) {
    for (auto *CoVL : VLI.getCoIteratingLoops(&VL))
      fillSubLoopMap(*CoVL, SubLoopMap);
  } else {
    fillSubLoopMap(VL, SubLoopMap);
  }

  DenseSet<Instruction *> TopLevelInsts;
  if (VL.isLoop()) {
    for (auto *CoVL : VLI.getCoIteratingLoops(&VL))
      for (auto *I : CoVL->getInstructions())
        TopLevelInsts.insert(I);
  } else {
    for (auto *I : VL.getInstructions())
      TopLevelInsts.insert(I);
  }

  std::function<void(SchedulerItem)> Schedule = [&](SchedulerItem Item) {
    bool Inserted = Reordered.insert(Item.getOpaqueValue()).second;
    if (!Inserted)
      return;

    auto *I = Item.dyn_cast<Instruction *>();
    // If I is contained in a sub loop, schedule the sub loop instead of
    // the instruction itself
    if (auto *SubVL = I ? SubLoopMap.lookup(Pkr.getVLoopFor(I)) : nullptr)
      return Schedule(SubVL);

    // If I is neither contained in a sub-loop nor a top-level instructions,
    // it must be from the parent loop, which is not our concern.
    if (I && !TopLevelInsts.count(I))
      return;

    auto *VP = Item.dyn_cast<const VectorPack *>();
    auto *SubVL = Item.dyn_cast<VLoop *>();

    // If we are coiterating this loop with some other loops, don't schedule
    // this loop on its own
    if (SubVL) {
      auto *LeaderVL = VLI.getCoIteratingLeader(SubVL);
      if (SubVL != LeaderVL)
        return Schedule(LeaderVL);
    }

    // Make sure all of the control-dependent conditions are scheduled
    if (Item.is<const ControlCondition *>()) {
      auto *C = Item.dyn_cast<const ControlCondition *>();
      if (auto *And = dyn_cast_or_null<ConditionAnd>(C)) {
        Schedule(And->Parent);
        if (auto *CondInst = dyn_cast<Instruction>(And->Cond))
          Schedule(CondInst);
      } else if (auto *Or = dyn_cast_or_null<ConditionOr>(C)) {
        for (auto *C2 : Or->Conds)
          Schedule(C2);
      }
      return;
    }

    // We need to reorder a packed instruction *together* with its pack
    if (auto *VP = I ? ValueToPackMap.lookup(I) : nullptr)
      return Schedule(VP);

    // Figure out the dependence
    std::vector<Value *> DependedValues;
    if (I) {
      // Make sure the control conditions are scheduled before the instruction
      Schedule(Pkr.getBlockCondition(I->getParent()));
      for (auto *V : VPCtx->iter_values(DA.getDepended(I))) {
        DependedValues.push_back(V);
      }
    } else if (VP) {
      // Make sure the control conditions are scheduled before the pack
      for (auto *V : VP->elementValues())
        Schedule(Pkr.getBlockCondition(cast<Instruction>(V)->getParent()));
      for (auto *V : VP->dependedValues())
        DependedValues.push_back(V);
    } else {
      assert(SubVL);
      // Make sure the control condition (guarding the loop preheader) are
      // scheduled first
      Schedule(SubVL->getLoopCond());
      for (auto *CoVL : VLI.getCoIteratingLoops(SubVL))
        for (auto *V : VPCtx->iter_values(CoVL->getDepended()))
          DependedValues.push_back(V);
    }

    // Recurse on the depended values
    for (auto *V : DependedValues)
      if (auto *I = dyn_cast<Instruction>(V))
        Schedule(I);

    // Now finalize ordering of this (pack of) instruction(s)
    if (I)
      return ScheduledItems.push_back(I);
    else if (SubVL)
      return ScheduledItems.push_back(SubVL);

    assert(VP);
    for (auto *V : VP->getOrderedValues())
      if (auto *I = dyn_cast_or_null<Instruction>(V))
        ScheduledItems.push_back(I);
  };

  for (auto *I : VL.getInstructions())
    if (isa<ReturnInst>(I) || !I->isTerminator())
      Schedule(I);
  for (auto &SubVL : VL.getSubLoops())
    Schedule(SubVL.get());

  if (VL.isLoop()) {
    for (auto *CoVL : VLI.getCoIteratingLoops(&VL)) {
      for (auto *I : CoVL->getInstructions())
        if (isa<ReturnInst>(I) || !I->isTerminator()) {

          Schedule(I);
        }
      for (auto &SubVL : CoVL->getSubLoops())
        Schedule(SubVL.get());
    }
  }

  return ScheduledItems;
}

static Value *emitReduction(RecurKind Kind, Value *A, Value *B,
                            IRBuilderBase &Builder) {
  switch (Kind) {
  case RecurKind::Add:
    return Builder.CreateAdd(A, B);
  case RecurKind::Mul:
    return Builder.CreateMul(A, B);
  case RecurKind::And:
    return Builder.CreateAnd(A, B);
  case RecurKind::Or:
    return Builder.CreateOr(A, B);
  case RecurKind::Xor:
    return Builder.CreateXor(A, B);
  case RecurKind::FAdd:
    return Builder.CreateFAdd(A, B);
  case RecurKind::FMul:
    return Builder.CreateFMul(A, B);

  case RecurKind::FMax:
    return Builder.CreateSelect(Builder.CreateFCmpOGT(A, B), A, B);
  case RecurKind::FMin:
    return Builder.CreateSelect(Builder.CreateFCmpOLT(A, B), A, B);

  case RecurKind::SMax:
    return Builder.CreateSelect(Builder.CreateICmpSGT(A, B), A, B);
  case RecurKind::SMin:
    return Builder.CreateSelect(Builder.CreateICmpSLT(A, B), A, B);

  case RecurKind::UMax:
    return Builder.CreateSelect(Builder.CreateICmpUGT(A, B), A, B);
  case RecurKind::UMin:
    return Builder.CreateSelect(Builder.CreateICmpULT(A, B), A, B);

  default:
    llvm_unreachable("unsupport reduction kind");
  }
  return nullptr;
}

// Move I to the end of BB
static void moveToEnd(Instruction *I, BasicBlock *BB) {
  I->removeFromParent();
  BB->getInstList().push_back(I);
  assert(I->getParent() == BB);
}

static PHINode *emitEta(Value *Init, Value *Iter, BasicBlock *Preheader,
                        BasicBlock *Header, BasicBlock *Latch) {
  auto *PN = PHINode::Create(Init->getType(), 2, "eta");
  PN->addIncoming(Init, Preheader);
  PN->addIncoming(Iter, Latch);
  Header->getInstList().push_front(PN);
  return PN;
}

static void fixDefUseDominance(Function *F, DominatorTree &DT) {
  // Find instructions not dominating their uses.
  // This happens when we move things across branches.
  DenseMap<Instruction *, SmallVector<Instruction *, 4>> BrokenUseDefs;
  for (Instruction &I : instructions(F)) {
    for (User *U : I.users()) {
      // Special case when the user is a phi-node
      if (auto *PN = dyn_cast<PHINode>(U)) {
        BasicBlock *IncomingBlock;
        Value *IncomingValue;
        for (auto Incoming : zip(PN->blocks(), PN->incoming_values())) {
          std::tie(IncomingBlock, IncomingValue) = Incoming;
          if (IncomingValue == &I &&
              !DT.dominates(I.getParent(), IncomingBlock)) {
            BrokenUseDefs[&I].push_back(PN);
            break;
          }
        }
        continue;
      }

      auto *UserInst = dyn_cast<Instruction>(U);
      if (UserInst && !DT.dominates(&I, UserInst))
        BrokenUseDefs[&I].push_back(UserInst);
    }
  }

  SmallVector<AllocaInst *> Allocas;
  for (auto &KV : BrokenUseDefs) {
    Instruction *I = KV.first;
    ArrayRef<Instruction *> Users = KV.second;

    auto *Alloca = new AllocaInst(I->getType(), 0, I->getName() + ".mem",
                                  &*F->getEntryBlock().getFirstInsertionPt());
    new StoreInst(I, Alloca, I->getNextNode());
    Allocas.push_back(Alloca);
    for (Instruction *UserInst : Users) {
      if (auto *PN = dyn_cast<PHINode>(UserInst)) {
        // Need to do the reload in predecessor for the phinodes
        for (unsigned i = 0; i < PN->getNumIncomingValues(); i++) {
          Value *V = PN->getIncomingValue(i);
          if (V != I)
            continue;
          auto *Reload = new LoadInst(
              I->getType(), Alloca, I->getName() + ".reload",
              PN->getIncomingBlock(i)->getTerminator() /*insert before*/);
          PN->setIncomingValue(i, Reload);
        }
        continue;
      }
      auto *Reload =
          new LoadInst(I->getType(), Alloca, I->getName() + ".reload",
                       UserInst /*insert before*/);
      UserInst->replaceUsesOfWith(I, Reload);
    }
  }

  PromoteMemToReg(Allocas, DT);
  assert(!verifyFunction(*F, &errs()));
}

std::pair<BasicBlock *, BasicBlock *>
VectorCodeGen::emitLoop(VLoop &VL, BasicBlock *Preheader) {
  BasicBlock *Header = nullptr;
  BasicBlock *Latch = nullptr;
  BasicBlock *Exit = nullptr;
  SmallVector<VLoop *, 4> CoIteratingLoops;
  auto &Ctx = Builder.getContext();

  if (VL.isLoop()) {
    Header = BasicBlock::Create(Ctx, "header", F);
    Latch = BasicBlock::Create(Ctx, "latch", F);
    Exit = BasicBlock::Create(Ctx, "exit", F);
    BranchInst::Create(Header /*if true*/, Preheader /*insert at end*/);

    // We will wire latch with exit and header later

    for (auto *CoVL : Pkr.getVLoopInfo().getCoIteratingLoops(&VL))
      CoIteratingLoops.push_back(CoVL);
  }

  DenseMap<VLoop *, const ControlCondition *> LoopActiveConds;
  DenseMap<VLoop *, PHINode *> LoopActivePhis;
  bool CoIterating = CoIteratingLoops.size() > 1;
  PHINode *ActiveVec = nullptr;
  if (CoIterating) {
    assert(Header);
    assert(Preheader);

    ControlDependenceAnalysis &CDA = Pkr.getCDA();

    // FIXME: call shouldVectorizeActiveConds instead
    bool VectorizeActiveConds = false;

    // Create a dummy phi to represent whether the a co-iterated loop is active
    auto *Int1Ty = Type::getInt1Ty(Ctx);
    SmallVector<PHINode *, 4> ActiveConds;
    for (auto *CoVL : CoIteratingLoops) {
      assert(ShouldEnterLoop.count(CoVL));
      auto *PN = PHINode::Create(Int1Ty, 2, "active", Header);
      // All the loops are active coming from the preheader.
      // We will specify the active conds coming from the latch later
      PN->addIncoming(ShouldEnterLoop.lookup(CoVL), Preheader);
      LoopActiveConds.try_emplace(CoVL, CDA.getAnd(nullptr, PN, true));
      LoopActivePhis.try_emplace(CoVL, PN);
      ActiveConds.push_back(PN);

      // If any of the back edge cond is packed, then we vectrozie the whole
      // active conds
      auto *And = dyn_cast<ConditionAnd>(CoVL->getBackEdgeCond());
      if (And && ValueToPackMap.count(And->Cond))
        VectorizeActiveConds = true;
    }

    if (VectorizeActiveConds) {
      assert(ShouldEnterLoopVec.count(&VL));
      // Also create a dummy vector
      // to represent the packed version of the active conds
      auto *ActiveVP = Pkr.getContext()->createPhiPack(
          ActiveConds, BitVector(), BitVector(), Pkr.getTTI());
      for (auto Item : enumerate(ActiveConds))
        ValueIndex[Item.value()] = {ActiveVP, (unsigned)Item.index(),
                                    Item.value()};
      auto *VecTy = FixedVectorType::get(Int1Ty, ActiveConds.size());
      ActiveVec = PHINode::Create(VecTy, 2, "active-pack", Header);
      ActiveVec->addIncoming(ShouldEnterLoopVec.lookup(&VL), Preheader);
      MaterializedPacks[ActiveVP] = ActiveVec;
    }
  }
  auto *MaybeLoopActiveConds = CoIterating ? &LoopActiveConds : nullptr;
  auto GetEta = [&](PHINode *PN) -> Optional<EtaNode> {
    for (auto *CoVL : CoIteratingLoops)
      if (auto MaybeEta = CoVL->getEta(PN))
        return MaybeEta;
    return None;
  };

  // For the top level "loop", the loop header is just the entry block
  // FIXME: use useScalar
  BlockBuilder BBuilder(VL.isLoop() ? Header : Entry, [&](Value *Cond) {
    auto It = ValueIndex.find(Cond);
    if (It == ValueIndex.end())
      return Cond;
    return It->second.Extracted;
  });
  DenseMap<const ControlCondition *, BasicBlock *> LastBlockForCond;
  DenseSet<BasicBlock *> LoopBlocks{Header, Exit, Latch};
  auto GetBlock = [&](const ControlCondition *C) {
    auto *BB = BBuilder.getBlockFor(C);
    LoopBlocks.insert(BB);
    LastBlockForCond[C] = BB;
    assert(!BB->getTerminator());
    return BB;
  };
  auto GetLastBlockFor = [&](const ControlCondition *C) {
    if (auto *BB = LastBlockForCond.lookup(C))
      return BB;
    return GetBlock(C);
  };

  SmallVector<std::pair<PHINode *, OperandPack>> EtasToPatch;
  auto &VLI = Pkr.getVLoopInfo();

  // Schedule the instructions and loops according to data dependence
  auto Schedule = schedule(VL.isLoop() ? *VLI.getCoIteratingLeader(&VL) : VL,
                           ValueToPackMap, Pkr);

  // Pick out the reduction packs, which we will emit last
  SmallPtrSet<const VectorPack *, 4> RdxPacks;
  // Also keep track of the reduction phis
  SmallPtrSet<PHINode *, 4> RdxPhis;
  SmallPtrSet<Value *, 4> OldRdxOps;
  for (auto &InstOrLoop : Schedule) {
    auto *I = InstOrLoop.dyn_cast<Instruction *>();
    if (!I)
      continue;
    auto *VP = ValueToPackMap.lookup(I);
    if (VP && VP->isReduction()) {
      auto &RI = VP->getReductionInfo();
      RdxPacks.insert(VP);
      RdxPhis.insert(RI.Phi);
      OldRdxOps.insert(RI.Ops.begin(), RI.Ops.end());
      if (RecurrenceDescriptor::isMinMaxRecurrenceKind(RI.Kind)) {
        for (auto *I : RI.Ops)
          OldRdxOps.insert(cast<SelectInst>(I)->getCondition());
      }
    }
  }
  assert((RdxPacks.empty() || !CoIterating) &&
         "can't do reduction while coiterating loops");

  // Scan the consectuive loads/stores and find those addresses that we need to
  // speculatively compute
  SmallPtrSet<const VectorPack *, 4> ConsecMemPacks;
  for (auto &InstOrLoop : Schedule) {
    auto *I = InstOrLoop.dyn_cast<Instruction *>();
    if (!I)
      continue;
    auto *VP = ValueToPackMap.lookup(I);
    if (VP && VP->getLoadStorePointer())
      ConsecMemPacks.insert(VP);
  }
  // Mapping address computation to the condition to speculate at
  DenseMap<Instruction *, const ControlCondition *> AddressesToSpeculate;
  for (auto *VP : ConsecMemPacks) {
    // Figure out the condition under which we should speculate the address
    SmallVector<const ControlCondition *, 8> Conds;
    for (auto *V : VP->elementValues())
      Conds.push_back(getBlockConditionAux(
          Pkr, cast<Instruction>(V)->getParent(), MaybeLoopActiveConds));
    auto *C = getGreatestCommonCondition(Conds);

    auto *Addr = getLoadStorePointerOperand(VP->getOrderedValues().front());
    auto *AddrComp = dyn_cast<Instruction>(Addr);

    // If the address doesn't come from an instruction, there's nothing to
    // speculate
    if (!AddrComp)
      continue;

    // If we always compute the address under condition C, we don't need to
    // speculate
    if (isImplied(getBlockConditionAux(Pkr, AddrComp->getParent(),
                                       MaybeLoopActiveConds),
                  C))
      continue;

    AddressesToSpeculate.try_emplace(AddrComp, C);
  }

  // If we are coiterating, and v is a live-out of a loop, return that loop
  auto GetLoopIfLiveOut = [&](Value *V) -> VLoop * {
    if (!CoIterating)
      return nullptr;
    auto *I = dyn_cast_or_null<Instruction>(V);
    if (!I)
      return nullptr;
    return Pkr.getVLoopFor(I);
    // FIXME: What follows is broken because it doesn't consider control
    // dependence
#if 0
    for (auto *CoVL : CoIteratingLoops)
      if (CoVL->isLiveOut(I))
        return CoVL;
    return nullptr;
#endif
  };

  DenseMap<Value *, AllocaInst *> ScalarLiveOutAllocas;
  auto GuardScalarLiveOut = [&](Value *V, VLoop *VL) {
    if (!CoIterating)
      return;

    // FIXME: this line is broken until we compute loop live-out properly
    if (!VL->isLiveOut(cast<Instruction>(V)))
      return;

    auto *BB = cast<Instruction>(V)->getParent();
    if (auto *Terminator = BB->getTerminator())
      Builder.SetInsertPoint(Terminator);
    else
      Builder.SetInsertPoint(BB);

    assert(LoopActivePhis.count(VL));
    auto *OutAlloca = new AllocaInst(
        V->getType(), 0, V->getName() + ".live-out", &Entry->front());

    auto *Prev = Builder.CreateLoad(V->getType(), OutAlloca);
    auto *Select = Builder.CreateSelect(LoopActivePhis.lookup(VL), V, Prev);
    Builder.CreateStore(Select, OutAlloca);
    Allocas.push_back(OutAlloca);
    ScalarLiveOutAllocas.try_emplace(V, OutAlloca);
  };

  DenseMap<const VectorPack *, AllocaInst *> LiveOutAllocas;
  auto GuardVectorLiveOut = [&](const VectorPack *VP, Value *V) {
    if (none_of(VP->getOrderedValues(), GetLoopIfLiveOut))
      return;

    setInsertAtEndOfBlock(Builder, cast<Instruction>(V)->getParent());
    auto *Mask = getMaskForInsts(VP->getOrderedValues(), MaybeLoopActiveConds);

    // Dedicated alloca (which we will promote later) to store the live-out
    auto *OutAlloca =
        new AllocaInst(V->getType(), 0, "vector-live-out", &Entry->front());

    auto *Prev = Builder.CreateLoad(V->getType(), OutAlloca);
    auto *Blend = Builder.CreateSelect(Mask, V, Prev);
    Builder.CreateStore(Blend, OutAlloca);
    Allocas.push_back(OutAlloca);
    LiveOutAllocas.try_emplace(VP, OutAlloca);
  };

  // Now generate code according to the schedule
  for (auto &InstOrLoop : Schedule) {
    // Emit the sub-loop recursively
    if (auto *SubVL = InstOrLoop.dyn_cast<VLoop *>()) {
      BasicBlock *SubLoopHeader, *SubLoopExit;
      SmallVector<const ControlCondition *, 8> Conds;
      for (auto *CoVL : VLI.getCoIteratingLoops(SubVL))
        Conds.push_back(getLoopCondAux(Pkr, CoVL, MaybeLoopActiveConds));

      // FIXME: consider the case that loop conds are identical
      const ControlCondition *LoopCond;
      BasicBlock *Preheader = nullptr;
      if (is_splat(Conds)) {
        LoopCond = Conds.front();
        Preheader = GetBlock(LoopCond);
        if (Conds.size() > 1) {
          for (auto *CoVL : VLI.getCoIteratingLoops(SubVL))
            ShouldEnterLoop[CoVL] = Builder.getTrue();
          ShouldEnterLoopVec[SubVL] =
              Builder.CreateVectorSplat(Conds.size(), Builder.getTrue());
        }
      } else if (Conds.size() > 1 && shouldVectorizeActiveConds(SubVL)) {
        LoopCond = getGreatestCommonCondition(Conds);
        Preheader = GetBlock(LoopCond);
        Builder.SetInsertPoint(Preheader);
        auto *ActiveVecInit =
            getOrEmitConditionPack(VPCtx->getConditionPack(Conds));
        ShouldEnterLoopVec[SubVL] = ActiveVecInit;
        // Extract the active vec's elements in case we need it
        assert(!Preheader->getTerminator());
        for (auto Item : enumerate(VLI.getCoIteratingLoops(SubVL)))
          ShouldEnterLoop[Item.value()] =
              Builder.CreateExtractElement(ActiveVecInit, Item.index());
      } else if (Conds.size() > 1) {
        if (Header)
          setInsertAtEndOfBlock(Builder, Header);
        else {
          assert(!VL.isLoop());
          setInsertAtEndOfBlock(Builder, Entry);
        }
        auto &Ctx = Builder.getContext();
        SmallVector<AllocaInst *, 8> ShouldEnterAllocas;
        for (auto Pair : zip(VLI.getCoIteratingLoops(SubVL), Conds)) {
          VLoop *CoVL = std::get<0>(Pair);
          const ControlCondition *Cond = std::get<1>(Pair);
          // Alloca indicatiung whether we should execute CoVL (which we are
          // coiterating)
          auto *ShouldEnterAlloca = Builder.CreateAlloca(
              Type::getInt1Ty(Ctx), nullptr /*array size*/, "should.enter");
          Allocas.push_back(ShouldEnterAlloca);
          ShouldEnterAllocas.push_back(ShouldEnterAlloca);

          // By default we should not execute CoVL
          Builder.CreateStore(ConstantInt::getFalse(Ctx), ShouldEnterAlloca);
        }

        for (auto Pair : zip(Conds, ShouldEnterAllocas)) {
          const ControlCondition *Cond = std::get<0>(Pair);
          Value *ShouldEnterAlloca = std::get<1>(Pair);

          // Unless its loop condition is true
          auto *BB = GetBlock(Cond);
          if (auto *Terminator = BB->getTerminator())
            new StoreInst(ConstantInt::getTrue(Ctx), ShouldEnterAlloca,
                          Terminator);
          else
            new StoreInst(ConstantInt::getTrue(Ctx), ShouldEnterAlloca, BB);
        }

        LoopCond = Pkr.getCDA().getOr(Conds);
        Preheader = GetBlock(LoopCond);
        for (auto Pair :
             zip(ShouldEnterAllocas, VLI.getCoIteratingLoops(SubVL))) {
          AllocaInst *ShouldEnterAlloca = std::get<0>(Pair);
          VLoop *CoVL = std::get<1>(Pair);
          ShouldEnterLoop[CoVL] =
              new LoadInst(Type::getInt1Ty(Ctx), ShouldEnterAlloca,
                           "should-enter", Preheader);
        }
      }

      // auto *LoopCond = SubVL->getLoopCond();
      // Use GetBlock???
      // auto *Preheader = BBuilder.getBlockFor(LoopCond);
      std::tie(SubLoopHeader, SubLoopExit) = emitLoop(*SubVL, Preheader);
      BBuilder.setBlockForCondition(SubLoopExit, LoopCond);
      LastBlockForCond[LoopCond] = SubLoopExit;
      continue;
    }

    auto *I = InstOrLoop.dyn_cast<Instruction *>();
    assert(I);

    auto *VLForInst = Pkr.getVLoopFor(I);
    auto *Cond =
        getBlockConditionAux(Pkr, I->getParent(), MaybeLoopActiveConds);
    auto *VP = ValueToPackMap.lookup(I);

    bool Speculated = false;
    auto It = AddressesToSpeculate.find(I);
    if (It != AddressesToSpeculate.end()) {
      moveToEnd(It->first, GetBlock(It->second));
      GuardScalarLiveOut(It->first, VLForInst);
      Speculated = true;
    }

    // I is not packed
    if (!VP || shouldSkip(VP)) {
      // Just drop these intrinsics
      if (m_Intrinsic<Intrinsic::experimental_noalias_scope_decl>(m_Value())
              .match(I) ||
          m_Intrinsic<Intrinsic::lifetime_start>(m_Value()).match(I) ||
          m_Intrinsic<Intrinsic::lifetime_end>(m_Value()).match(I)) {
        I->eraseFromParent();
        continue;
      }

      // We've moved this instruction already
      if (Speculated)
        continue;

      // I is being reduced by a reduction pack so will be dead later
      if (OldRdxOps.count(I))
        continue;

      auto *PN = dyn_cast<PHINode>(I);
      if (!PN) {
        moveToEnd(I, GetBlock(Cond));
        GuardScalarLiveOut(I, VLForInst);
        continue;
      }

      // Skip reduction phis, which will become dead after vectorization
      if (RdxPhis.count(PN))
        continue;

      if (auto EtaOrNone = GetEta(PN)) {
        auto &Eta = *EtaOrNone;
        assert(Header && Exit);
        auto *NewPN =
            emitEta(useScalar(Eta.Init), Eta.Iter, Preheader, Header, Latch);
        // FIXME: this is broken: when we are co-iterating, only do this for uses in side the loops
        PN->replaceAllUsesWith(NewPN);
        GuardScalarLiveOut(NewPN, VLForInst);
        ReplacedPHIs[PN] = NewPN;
        continue;
      }

      // Demote the phi to memory
      auto *Alloca = new AllocaInst(
          PN->getType(), 0, PN->getName() + ".demoted", &Entry->front());
      Allocas.push_back(Alloca);
      for (unsigned i = 0; i < PN->getNumIncomingValues(); i++) {
        auto *EdgeCond = getEdgeCondAux(Pkr, PN->getIncomingBlock(i),
                                        PN->getParent(), MaybeLoopActiveConds);
        setInsertAtEndOfBlock(Builder, GetLastBlockFor(EdgeCond));
        Builder.CreateStore(PN->getIncomingValue(i), Alloca);
      }
      Builder.SetInsertPoint(GetBlock(Cond));
      auto *Reload = Builder.CreateLoad(PN->getType(), Alloca);
      PN->replaceAllUsesWith(Reload);
      ReplacedPHIs[PN] = Reload;
      GuardScalarLiveOut(Reload, VLForInst);
      continue;
    }

    // I is packed but we've already lowered that pack
    if (MaterializedPacks.count(VP))
      continue;

    // Delay reduction until last
    if (VP->isReduction())
      continue;

    // Get or create a new basic block to emit the pack
    SmallVector<const ControlCondition *, 8> Conds;
    for (auto *V : VP->elementValues())
      Conds.push_back(getBlockConditionAux(
          Pkr, cast<Instruction>(V)->getParent(), MaybeLoopActiveConds));

    Value *VecInst;
    if (VP->isGamma()) {
      Builder.SetInsertPoint(GetBlock(getGreatestCommonCondition(Conds)));

      // Special case to emit gamma pack
      ArrayRef<const GammaNode *> Gammas = VP->getGammas();
      unsigned NumIncomings = Gammas.front()->PN->getNumIncomingValues();
      assert(all_of(Gammas, [&](auto *G2) {
        return G2->PN->getNumIncomingValues() == NumIncomings;
      }));

      SmallVector<Value *, 8> GateConds, GateVals;
      for (unsigned i = 0; i < NumIncomings; i++) {
        SmallVector<const ControlCondition *> Conds;
        OperandPack Vals;
        for (auto *G : Gammas) {
          Conds.push_back(G->Conds[i]);
          Vals.push_back(G->Vals[i]);
        }
        auto *CP = VPCtx->getConditionPack(Conds);
        GateConds.push_back(getOrEmitConditionPack(CP));
        GateVals.push_back(gatherOperandPack(Vals));
      }
      auto *Sel = GateVals.back();
      auto CondsAndVals =
          drop_begin(zip(reverse(GateConds), reverse(GateVals)));
      Value *C, *V;
      for (auto CondAndVal : CondsAndVals) {
        std::tie(C, V) = CondAndVal;
        Sel = Builder.CreateSelect(C, V, Sel);
      }
      VecInst = Sel;
    } else if (VP->isPHI()) {
      // Special case when we are packing loop phis
      if (GetEta(cast<PHINode>(VP->getOrderedValues().front()))) {
        OperandPack InitOP, IterOP;
        for (auto *V : VP->getOrderedValues()) {
          auto MaybeEta = GetEta(cast<PHINode>(V));
          assert(MaybeEta);
          InitOP.push_back(MaybeEta->Init);
          IterOP.push_back(MaybeEta->Iter);
        }
        assert(Preheader && Preheader->getTerminator());
        Builder.SetInsertPoint(Preheader->getTerminator());
        auto *InitVec = gatherOperandPack(InitOP);
        assert(Latch);
        auto *Eta = emitEta(InitVec, UndefValue::get(getVectorType(*VP)),
                            Preheader, Header, Latch);
        EtasToPatch.emplace_back(Eta, IterOP);
        VecInst = Eta;
      } else {
        auto *PN = cast<PHINode>(*VP->elementValues().begin());
        auto *VecTy = getVectorType(*VP);
        auto *Alloca = new AllocaInst(VecTy, 0, PN->getName() + ".vector",
                                      &Entry->front());
        // Track the alloca so we can promote it back to phi later
        Allocas.push_back(Alloca);

        ArrayRef<const OperandPack *> OPs = VP->getOperandPacks();

        for (unsigned i = 0; i < PN->getNumIncomingValues(); i++) {
          auto *Cond =
              Pkr.getEdgeCondition(PN->getIncomingBlock(i), PN->getParent());
          auto *BB = GetLastBlockFor(Cond);
          if (auto *Terminator = BB->getTerminator())
            Builder.SetInsertPoint(Terminator);
          else
            Builder.SetInsertPoint(BB);
          auto *Gathered = gatherOperandPack(*OPs[i]);
          Builder.CreateStore(Gathered, Alloca);
        }

        Builder.SetInsertPoint(GetBlock(getGreatestCommonCondition(Conds)));
        VecInst = Builder.CreateLoad(VecTy, Alloca, "reload");
      }
    } else {
      Builder.SetInsertPoint(GetBlock(getGreatestCommonCondition(Conds)));

      // For other instructions, we just get gather their operands and
      // emit the vector instruction Get the operands ready.
      SmallVector<Value *, 2> Operands;
      for (auto *OP : VP->getOperandPacks()) {
        Operands.push_back(gatherOperandPack(*OP));
      }

      // Now we can emit the vector instruction
      ArrayRef<Value *> Vals = VP->getOrderedValues();
      if (VP->isLoad())
        VecInst = VP->emitVectorLoad(
            Operands, getMaskForInsts(Vals, MaybeLoopActiveConds), Builder);
      else if (VP->isStore()) {
        VecInst = VP->emitVectorStore(
            Operands, getMaskForInsts(Vals, MaybeLoopActiveConds), Builder);
      } else
        VecInst = VP->emit(Operands, Builder);
    }

    // Conservatively extract all elements.
    // Let the later cleanup passes clean up dead extracts.
    if (!VP->isStore() && !VP->isReduction()) {
      setInsertAtEndOfBlock(Builder, cast<Instruction>(VecInst)->getParent());
      for (auto &Item : enumerate(VP->getOrderedValues())) {
        if (auto *V = Item.value()) {
          unsigned i = Item.index();
          auto *Extract = Builder.CreateExtractElement(VecInst, i);
          if (!CoIterating)
            V->replaceAllUsesWith(Extract);
          else {
            // Only replace uses of V with extract for users inside the loop
            V->replaceUsesWithIf(Extract, [&](Use &U) {
                auto *I = dyn_cast<Instruction>(U.getUser());
                return !I || count_if(CoIteratingLoops, [&](auto *CoVL) {
                    return Pkr.getVLoopFor(I) == CoVL; });
                });
          }
          ValueIndex[V] = {VP, i, Extract};
        }
      }
    }

    if (CoIterating && !VP->isStore()) {
      // setInsertAtEndOfBlock(Builder, cast<Instruction>(VecInst->getParent());
      GuardVectorLiveOut(VP, VecInst);
    }

    // Map the pack to its materialized value
    MaterializedPacks[VP] = VecInst;
  }

  if (!VL.isLoop())
    return {nullptr, nullptr};

  // Emit the reductions.
  auto *TTI = Pkr.getTTI();
  assert(RdxPacks.empty() || VL.isLoop());
  for (auto *VP : RdxPacks) {
    ArrayRef<const OperandPack *> OPs = VP->getOperandPacks();
    auto *VecTy = getVectorType(*OPs.front());
    auto &RI = VP->getReductionInfo();

    SmallVector<PHINode *, 4> VecPhis;
    SmallVector<Value *, 4> RdxOps;
    for (auto *OP : OPs) {
      // Emit the vector phi, specify the incomings later
      Builder.SetInsertPoint(&Header->front());
      auto *VecPhi = Builder.CreatePHI(VecTy, 2 /*num incoming*/);
      VecPhis.push_back(VecPhi);

      // Gather operand in the latch
      Builder.SetInsertPoint(Latch);
      auto *Operand = gatherOperandPack(*OP);
      RdxOps.push_back(emitReduction(RI.Kind, VecPhi, Operand, Builder));
    }

    // Patch up the vector phi
    Value *IdentityVector;
    if (RecurrenceDescriptor::isMinMaxRecurrenceKind(RI.Kind)) {
      Builder.SetInsertPoint(Preheader->getTerminator());
      IdentityVector = Builder.CreateVectorSplat(VecTy->getElementCount(),
                                                 useScalar(RI.StartValue));
    } else {
      auto *Identity = RecurrenceDescriptor::getRecurrenceIdentity(
          RI.Kind, RI.Phi->getType());
      IdentityVector =
          ConstantVector::getSplat(VecTy->getElementCount(), Identity);
    }

    for (auto Pair : zip(VecPhis, RdxOps)) {
      PHINode *VecPhi = std::get<0>(Pair);
      Value *RdxOp = std::get<1>(Pair);
      VecPhi->addIncoming(IdentityVector, Preheader);
      VecPhi->addIncoming(RdxOp, Latch);
    }

    // Do horizontal-reduction on the vector in the exit block
    //// Reduce the vector in the exit block
    Builder.SetInsertPoint(Exit);
    Value *RdxOp = RdxOps.front();
    for (auto *RdxOp2 : drop_begin(RdxOps))
      RdxOp = emitReduction(RI.Kind, RdxOp, RdxOp2, Builder);

    auto *HorizontalRdx =
        createSimpleTargetReduction(Builder, TTI, RdxOp, RI.Kind);
    auto *Reduced = emitReduction(RI.Kind, HorizontalRdx,
                                  useScalar(RI.StartValue), Builder);
    RI.Ops.front()->replaceAllUsesWith(Reduced);
  }

  AllocaInst *ContAlloca = nullptr;
  DenseMap<VLoop *, AllocaInst *> ScalarActiveConds;
  if (!ActiveVec) {
    auto &Ctx = Builder.getContext();
    ContAlloca = new AllocaInst(Type::getInt1Ty(Ctx), 0, "continue_cond",
                                Header->getFirstNonPHI());
    Allocas.push_back(ContAlloca);
    // By default, we don't continue
    if (auto HeaderTerminator = Header->getTerminator())
      new StoreInst(ConstantInt::getFalse(Ctx), ContAlloca, HeaderTerminator);
    else
      new StoreInst(ConstantInt::getFalse(Ctx), ContAlloca, Header);

    // Continue if ...
    if (CoIterating) {
      for (auto *CoVL : CoIteratingLoops) {
        auto *StillActive = Pkr.getCDA().concat(
            MaybeLoopActiveConds->lookup(CoVL), CoVL->getBackEdgeCond());
        new StoreInst(ConstantInt::getTrue(Ctx), ContAlloca,
                      GetBlock(StillActive));

        auto *ActiveCond = new AllocaInst(Type::getInt1Ty(Ctx), 0, "active",
                                          Header->getFirstNonPHI());

        if (auto HeaderTerminator = Header->getTerminator())
          new StoreInst(ConstantInt::getFalse(Ctx), ActiveCond,
                        HeaderTerminator);
        else
          new StoreInst(ConstantInt::getFalse(Ctx), ActiveCond, Header);

        Allocas.push_back(ActiveCond);
        new StoreInst(ConstantInt::getTrue(Ctx), ActiveCond,
                      GetBlock(StillActive));
        ScalarActiveConds.try_emplace(CoVL, ActiveCond);
      }
    } else {
      new StoreInst(ConstantInt::getTrue(Ctx), ContAlloca,
                    GetBlock(VL.getBackEdgeCond()));
    }

#if 0
    // Also keep track of whether each co-iterating loops are individually
    // active
    for (auto *CoVL : CoIteratingLoops) {
      auto *ActiveCond = new AllocaInst(Type::getInt1Ty(Ctx), 0, "active",
                                        Header->getFirstNonPHI());

      if (auto HeaderTerminator = Header->getTerminator())
        new StoreInst(ConstantInt::getFalse(Ctx), ActiveCond, HeaderTerminator);
      else
        new StoreInst(ConstantInt::getFalse(Ctx), ActiveCond, Header);

      Allocas.push_back(ActiveCond);
      new StoreInst(ConstantInt::getTrue(Ctx), ActiveCond,
                    GetBlock(CoVL->getBackEdgeCond()));
      ScalarActiveConds.try_emplace(CoVL, ActiveCond);
    }
#endif
  }

  // Join everything to the latch
  BranchInst::Create(Latch, GetBlock(nullptr));
  Builder.SetInsertPoint(Latch);

  // Patch the eta nodes
  for (auto &Pair : EtasToPatch) {
    PHINode *Eta = Pair.first;
    OperandPack &IterOP = Pair.second;
    Eta->setIncomingValue(1, gatherOperandPack(IterOP));
  }

  Value *ShouldContinue = nullptr;
  if (!ActiveVec) {
    ShouldContinue = Builder.CreateLoad(Type::getInt1Ty(Ctx), ContAlloca);
  } else {
    SmallVector<const ControlCondition *, 8> BackEdgeConds;
    for (auto *CoVL : CoIteratingLoops)
      BackEdgeConds.push_back(CoVL->getBackEdgeCond());
    auto *NextActiveVec = Builder.CreateAnd(
        ActiveVec,
        getOrEmitConditionPack(VPCtx->getConditionPack(BackEdgeConds)));
    // Patch up the active conds vector phi
    ActiveVec->addIncoming(NextActiveVec, Latch);
    // We should continue if at least one of the co-iterating loops is active
    ShouldContinue = Builder.CreateOrReduce(NextActiveVec);
    for (auto Item : enumerate(CoIteratingLoops)) {
      unsigned i = Item.index();
      VLoop *CoVL = Item.value();
      assert(LoopActivePhis.count(CoVL));
      LoopActivePhis.lookup(CoVL)->addIncoming(
          Builder.CreateExtractElement(ActiveVec, i), Latch);
    }
  }

  if (CoIterating && !ActiveVec) {
    for (auto *CoVL : CoIteratingLoops) {
      assert(LoopActivePhis.count(CoVL));
      LoopActivePhis.lookup(CoVL)->addIncoming(
          Builder.CreateLoad(ScalarActiveConds.lookup(CoVL)), Latch);
    }
  }

  Builder.CreateCondBr(ShouldContinue, Header, Exit);

  assert(!Exit->getTerminator());
  Builder.SetInsertPoint(Exit);

  for (auto KV : LiveOutAllocas) {
    auto *VP = KV.first;
    auto *Alloca = KV.second;
    auto *Reload = Builder.CreateLoad(getVectorType(*VP), Alloca);

    for (auto &Item : enumerate(VP->getOrderedValues())) {
      if (auto *V = Item.value()) {
        unsigned i = Item.index();
        auto *Extract = Builder.CreateExtractElement(Reload, i);
        V->replaceAllUsesWith(Extract);
        ValueIndex[V] = {VP, i, Extract};
      }
    }
    MaterializedPacks[VP] = Reload;
  }

  SmallPtrSet<VLoop *, 8> CoIteratingLoopSet(CoIteratingLoops.begin(),
                                             CoIteratingLoops.end());
  for (auto KV : ScalarLiveOutAllocas) {
    Value *V = KV.first;
    auto *Alloca = KV.second;
    auto *Reload =
        Builder.CreateLoad(V->getType(), Alloca, Alloca->getName() + ".reload");
    V->replaceUsesWithIf(Reload, [&](Use &U) {
      auto *I = dyn_cast<Instruction>(U.getUser());
      return !I || !LoopBlocks.count(I->getParent());
    });
    ReplacedUses.try_emplace(V, Reload);
  }

  return {Header, Exit};
};

void VectorCodeGen::run() {
  // Keep track of the old basic blocks, which we will remove after we are done
  std::vector<BasicBlock *> OldBlocks;
  for (auto &BB : *F)
    OldBlocks.push_back(&BB);

  // Allocate a new dedicated entry block
  Entry = BasicBlock::Create(Builder.getContext(), "entry", F);

  // Emit the top level loop, which will then recursively the sub loops
  emitLoop(Pkr.getTopVLoop(), nullptr);

  if (DumpBeforeErasingOldBlocks)
    F->dump();

  // Remove the old blocks
  for (auto *BB : OldBlocks)
    for (auto &I : *BB)
      I.dropAllReferences();
  for (auto *BB : OldBlocks)
    BB->eraseFromParent();

  if (DumpAfterErasingOldBlocks)
    F->dump();

  // Restore SSA
  DominatorTree DT(*F);
  PromoteMemToReg(Allocas, DT);
  fixDefUseDominance(F, DT);

  // Delete trivially dead instructions
  bool Changed;
  do {
    SmallVector<Instruction *> ReallyDeadInsts;
    for (Instruction &I : instructions(F))
      if (isInstructionTriviallyDead(&I))
        ReallyDeadInsts.push_back(&I);
    for (auto *I : ReallyDeadInsts)
      I->eraseFromParent();
    Changed = !ReallyDeadInsts.empty();
  } while (Changed);
}

void VectorPackSet::codegen(IntrinsicBuilder &Builder, Packer &Pkr) {
  if (AllPacks.empty() && !RescheduleScalars)
    return;

  // Fuse the loops for packs involving multiple loops
  for (auto *VP : AllPacks) {
    auto *VL = Pkr.getVLoopFor(cast<Instruction>(*VP->elementValues().begin()));
    for (auto *V : VP->elementValues()) {
      auto *VL2 = Pkr.getVLoopFor(cast<Instruction>(V));
      if (VL != VL2)
        Pkr.fuseOrCoIterateLoops(VL, VL2);
    }
  }

  VectorCodeGen CodeGen(Pkr, Builder, ValueToPackMap);
  CodeGen.run();
}
