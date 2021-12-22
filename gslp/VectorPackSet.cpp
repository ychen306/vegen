#include "VectorPackSet.h"
#include "BlockBuilder.h"
#include "ControlDependence.h"
#include "ControlReifier.h"
#include "Heuristic.h"
#include "Packer.h"
#include "Plan.h"
#include "Solver.h"
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

extern cl::opt<bool> TestCodeGen;

static cl::opt<bool> DumpAfterErasingOldBlocks("dump-after-erasing-old-blocks",
                                               cl::init(false));

static cl::opt<bool>
    DumpBeforeErasingOldBlocks("dump-before-erasing-old-blocks",
                               cl::init(false));

static bool shouldSkip(const VectorPack *VP) {
#if 0
  return !(VP->isLoad() || VP->isStore());
  return true;
#endif
  return false;
  // return VP->getProducer() &&
  // VP->getProducer()->getName().contains("builtin");
}

namespace {

class VectorCodeGen {
  Packer &Pkr;
  const VectorPackContext *VPCtx;
  Function *F;
  BasicBlock *Entry;
  IntrinsicBuilder &Builder;
  ControlReifier &Reifier;
  const DenseMap<Value *, const VectorPack *> &ValueToPackMap;

  DenseMap<const llvm::Value *, VectorPackIndex> ValueIndex;
  PackToValueTy MaterializedPacks;
  // Instead of moving PHIs around,
  // we will demote them and implement control-flow join through memory
  DenseMap<PHINode *, Value *> ReplacedPHIs;
  SmallVector<PHINode *> OneHotPhis;
  SmallVector<PHINode *> MuNodes;
  // Track the last used block for a given condition,
  // these are the blocks where we will store the incoming values to the demoted
  // allocas.
  SmallVector<AllocaInst *> Allocas;
  DenseMap<Value *, Value *> ReplacedUses;
  DenseMap<Value *, Value *> GuardedLiveOuts;

  Value *gatherOperandPack(const OperandPack &OP);
  Value *getOrEmitMask(ArrayRef<const ControlCondition *>, VLoop *);
  Value *getLoadStoreMask(ArrayRef<Value *>, VLoop *);

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

  void fixScalarUses(Instruction *I) {
    for (unsigned i = 0; i < I->getNumOperands(); i++) {
      auto *V = I->getOperand(i);
      if (auto *Guarded = GuardedLiveOuts.lookup(V))
        V = Guarded;
      I->setOperand(i, useScalar(V));
    }
  }

  Value *getReifiedBackEdgeCond(VLoop *VL) {
    auto *BEC = VL->getBackEdgeCond();
    if (!BEC)
      return Builder.getTrue();

    auto *Or = dyn_cast<ConditionOr>(BEC);

    // If none of the reified sub-terms of the disjunction
    // is packed, we will just use the scalar reified value
    auto IsPacked = [&](const ControlCondition *C) {
      return ValueToPackMap.count(Reifier.getValue(C, VL));
    };
    if (!Or || none_of(Or->Conds, IsPacked))
      return useScalar(Reifier.getValue(BEC, VL));

    // If some of the conditions are packed, we will vectorize
    OperandPack OP;
    for (auto *C : Or->Conds)
      OP.push_back(Reifier.getValue(C, VL));
    return Builder.CreateOrReduce(gatherOperandPack(OP));
  }

public:
  VectorCodeGen(Packer &Pkr, IntrinsicBuilder &Builder, ControlReifier &Reifier,
                const DenseMap<Value *, const VectorPack *> &ValueToPackMap)
      : Pkr(Pkr), VPCtx(Pkr.getContext()), F(Pkr.getFunction()), Entry(nullptr),
        Builder(Builder), Reifier(Reifier), ValueToPackMap(ValueToPackMap) {}

  void run();
};
} // namespace

static void setInsertAtEndOfBlock(IRBuilderBase &Builder, BasicBlock *BB) {
  if (auto *Terminator = BB->getTerminator())
    Builder.SetInsertPoint(Terminator);
  else
    Builder.SetInsertPoint(BB);
}

static void getLoadStoreConds(SmallVectorImpl<const ControlCondition *> &Conds,
                              ArrayRef<Value *> Vals, VLoop *VL) {
  auto *SomeInst =
      cast<Instruction>(*find_if(Vals, [](Value *V) { return V; }));
  auto *C = VL->getInstCond(SomeInst);
  for (auto *V : Vals)
    Conds.push_back(V ? VL->getInstCond(cast<Instruction>(V)) : C);
}

Value *VectorCodeGen::getLoadStoreMask(ArrayRef<Value *> Vals, VLoop *VL) {
  SmallVector<const ControlCondition *> Conds;
  getLoadStoreConds(Conds, Vals, VL);
  // If the vectorized accesses have the same conditions, we don't need a mask
  if (is_splat(Conds))
    return nullptr;
  return getOrEmitMask(Conds, VL);
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
  // FIXME: use guarded loop live out whenever necessary
  for (unsigned i = 0; i < NumValues; i++) {
    auto *V = OP[i];
    if (auto *Guarded = GuardedLiveOuts.lookup(V))
      V = Guarded;

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

Value *VectorCodeGen::getOrEmitMask(ArrayRef<const ControlCondition *> Conds,
                                    VLoop *VL) {
  OperandPack Vals;
  for (auto *C : Conds)
    Vals.push_back(Reifier.getValue(C, VL));
  return gatherOperandPack(Vals);
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

// Topsort the instructions s.t. instructions in the same packs are grouped
// together.
static std::vector<PointerUnion<Instruction *, VLoop *>>
schedule(VLoop &VL, ControlReifier &Reifier,
         const DenseMap<Value *, const VectorPack *> &ValueToPackMap,
         Packer &Pkr) {
  auto &DA = Pkr.getDA();
  auto &VLI = Pkr.getVLoopInfo();

  // Schedule the instruction to the pack dependence.
  // In particular, we want the instructions to be packed stay together.
  const VectorPackContext *VPCtx = Pkr.getContext();
  using SchedulerItem = PointerUnion<Instruction *, const VectorPack *,
                                     const ControlCondition *, VLoop *>;
  // mapping a nested loop to the *sub loop of VL* that contains it
  DenseMap<VLoop *, VLoop *> SubLoopMap;
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

  DenseSet<Instruction *> TopLevelInsts(VL.inst_begin(), VL.inst_end());

  DenseSet<void *> Reordered;
  std::vector<PointerUnion<Instruction *, VLoop *>> ScheduledItems;
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

    // Make sure all of the control-dependent conditions are scheduled
    if (Item.is<const ControlCondition *>()) {
      auto *C = Item.dyn_cast<const ControlCondition *>();
      if (auto *I = dyn_cast<Instruction>(Reifier.getValue(C, &VL))) {
        Schedule(I);
      }
#if 0
      auto *And = dyn_cast_or_null<ConditionAnd>(C);
      if (And) {
        if (auto *I = dyn_cast<Instruction>(Reifier.getValue(And->Complement, &VL))) {
          Schedule(I);
        }
      }
#endif
      return;
    }

    // We need to reorder a packed instruction *together* with its pack
    if (auto *VP = I ? ValueToPackMap.lookup(I) : nullptr)
      return Schedule(VP);

    // Figure out the dependence
    std::vector<Value *> DependedValues;
    if (I) {
      // Make sure the control conditions are scheduled before the instruction
      Schedule(VL.getInstCond(I));
      for (auto *V : VPCtx->iter_values(DA.getDepended(I))) {
        DependedValues.push_back(V);
      }
    } else if (VP) {
      // Make sure the control conditions are scheduled before the pack
      for (auto *V : VP->elementValues()) {
        Schedule(VL.getInstCond(cast<Instruction>(V)));
        auto *PN = dyn_cast<PHINode>(V);
        if (!PN)
          continue;
        if (VL.isGatedPhi(PN)) {
          for (unsigned i = 0; i < PN->getNumIncomingValues(); i++)
            Schedule(VL.getIncomingPhiCondition(PN, i));
        } else if (auto OneHot = VL.getOneHotPhi(PN)) {
          for (unsigned i = 0; i < PN->getNumIncomingValues(); i++)
            Schedule(OneHot->C);
        }
      }
      for (auto *V : VP->dependedValues())
        DependedValues.push_back(V);
    } else {
      assert(SubVL);
      // Make sure the control condition (guarding the loop preheader) are
      // scheduled first
      Schedule(SubVL->getLoopCond());
      for (auto *V : VPCtx->iter_values(SubVL->getDepended()))
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

  SmallVector<PHINode *> Mus;
  SmallVector<Instruction *> Insts, Returns;
  Instruction *Ret = nullptr;
  for (auto *I : VL.getInstructions()) {
    auto *PN = dyn_cast<PHINode>(I);
    if (PN && VL.getMu(PN))
      Mus.push_back(PN);
    else if (!I->isTerminator())
      Insts.push_back(I);
    else if (isa<ReturnInst>(I))
      Returns.push_back(I);
  }

  for (auto *PN : Mus)
    Schedule(PN);
  for (auto *I : Insts)
    Schedule(I);
  for (auto &SubVL : VL.getSubLoops())
    Schedule(SubVL.get());
  for (auto *Ret : Returns)
    Schedule(Ret);

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
  if (I->getParent())
    I->removeFromParent();
  BB->getInstList().push_back(I);
  assert(I->getParent() == BB);
}

static PHINode *emitMu(Value *Init, Value *Iter, BasicBlock *Preheader,
                       BasicBlock *Header, BasicBlock *Latch) {
  auto *PN = PHINode::Create(Init->getType(), 2, "mu");
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
  auto &Ctx = Builder.getContext();

  if (VL.isLoop()) {
    Header = BasicBlock::Create(Ctx, "header", F);
    Latch = BasicBlock::Create(Ctx, "latch", F);
    Exit = BasicBlock::Create(Ctx, "exit", F);
    BranchInst::Create(Header /*if true*/, Preheader /*insert at end*/);
    // We will wire latch with exit and header later
  }

  // For the top level "loop", the loop header is just the entry block
  // FIXME: use useScalar
  BlockBuilder BBuilder(VL.isLoop() ? Header : Entry, [&](Value *Cond) {
    return useScalar(Cond);
#if 0
    auto It = ValueIndex.find(Cond);
    if (It == ValueIndex.end())
      return Cond;
    return It->second.Extracted;
#endif
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

  SmallVector<std::pair<PHINode *, OperandPack>> MusToPatch;
  SmallVector<std::pair<PHINode *, Value *>> ScalarMusToPatch;
  auto &VLI = Pkr.getVLoopInfo();

  // Schedule the instructions and loops according to data dependence
  auto Schedule = schedule(VL, Reifier, ValueToPackMap, Pkr);

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

  // Now generate code according to the schedule
  for (auto &InstOrLoop : Schedule) {
    // Emit the sub-loop recursively
    if (auto *SubVL = InstOrLoop.dyn_cast<VLoop *>()) {
      BasicBlock *SubLoopHeader, *SubLoopExit;
      auto *LoopCond = SubVL->getLoopCond();
      BasicBlock *Preheader = GetBlock(LoopCond);
      std::tie(SubLoopHeader, SubLoopExit) = emitLoop(*SubVL, Preheader);
      BBuilder.setBlockForCondition(SubLoopExit, LoopCond);
      LastBlockForCond[LoopCond] = SubLoopExit;
      continue;
    }

    auto *I = InstOrLoop.dyn_cast<Instruction *>();
    assert(I);

    auto *Cond = VL.getInstCond(I);
    auto *VP = ValueToPackMap.lookup(I);

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

      // I is being reduced by a reduction pack so will be dead later
      if (OldRdxOps.count(I))
        continue;

      auto *PN = dyn_cast<PHINode>(I);
      if (!PN) {
        fixScalarUses(I);
        moveToEnd(I, GetBlock(Cond));
        continue;
      }

      // Skip reduction phis, which will become dead after vectorization
      if (RdxPhis.count(PN))
        continue;

      // FIXME: do something like MusToPatch but for scalars
      if (auto MuOrNone = VL.getMu(PN)) {
        auto &Mu = *MuOrNone;
        assert(Header && Exit);
        auto *NewPN =
            emitMu(useScalar(Mu.Init), Mu.Iter, Preheader, Header, Latch);
        ScalarMusToPatch.emplace_back(NewPN, Mu.Iter);
        ReplacedPHIs[PN] = NewPN;
        if (!PN->getParent())
          MuNodes.push_back(PN);
        continue;
      }

      // Demote the phi to memory
      auto *Alloca = new AllocaInst(
          PN->getType(), 0, PN->getName() + ".demoted", &Entry->front());
      Allocas.push_back(Alloca);
      if (auto MaybeOneHot = VL.getOneHotPhi(PN)) {
        Builder.SetInsertPoint(GetBlock(nullptr));
        Builder.CreateStore(useScalar(MaybeOneHot->IfFalse), Alloca);
        Builder.SetInsertPoint(GetBlock(MaybeOneHot->C));
        Builder.CreateStore(useScalar(MaybeOneHot->IfTrue), Alloca);
        OneHotPhis.push_back(PN);
      } else {
        for (unsigned i = 0; i < PN->getNumIncomingValues(); i++) {
          auto *EdgeCond = VL.getIncomingPhiCondition(PN, i);
          setInsertAtEndOfBlock(Builder, GetBlock(EdgeCond));
          Builder.CreateStore(useScalar(PN->getIncomingValue(i)), Alloca);
        }
      }
      Builder.SetInsertPoint(GetBlock(Cond));
      auto *Reload = Builder.CreateLoad(PN->getType(), Alloca);
      ReplacedPHIs[PN] = Reload;
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
      Conds.push_back(VL.getInstCond(cast<Instruction>(V)));

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
          Conds.push_back(VL.getIncomingPhiCondition(G->PN, i));
          Vals.push_back(G->Vals[i]);
        }
        GateConds.push_back(getOrEmitMask(Conds, &VL));
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
      auto *SomePhi = cast<PHINode>(VP->getOrderedValues().front());
      if (VL.getMu(SomePhi)) {
        OperandPack InitOP, IterOP;
        for (auto *V : VP->getOrderedValues()) {
          auto *PN = cast<PHINode>(V);
          auto MaybeMu = VL.getMu(PN);
          assert(MaybeMu);
          if (!PN->getParent())
            MuNodes.push_back(PN);
          InitOP.push_back(MaybeMu->Init);
          IterOP.push_back(MaybeMu->Iter);
        }
        assert(Preheader && Preheader->getTerminator());
        Builder.SetInsertPoint(Preheader->getTerminator());
        auto *InitVec = gatherOperandPack(InitOP);
        assert(Latch);
        auto *Mu = emitMu(InitVec, UndefValue::get(getVectorType(*VP)),
                          Preheader, Header, Latch);
        MusToPatch.emplace_back(Mu, IterOP);
        VecInst = Mu;
        VecInst->setName(SomePhi->getName());
      } else if (VL.getOneHotPhi(SomePhi)) {
        SmallVector<const ControlCondition *, 8> Conds;
        OperandPack IfTrue, IfFalse;
        for (auto *V : VP->getOrderedValues()) {
          auto *PN = cast<PHINode>(V);
          OneHotPhis.push_back(PN);
          auto OneHot = VL.getOneHotPhi(PN);
          assert(OneHot);
          Conds.push_back(OneHot->C);
          IfTrue.push_back(OneHot->IfTrue);
          IfFalse.push_back(OneHot->IfFalse);
        }
        Builder.SetInsertPoint(GetBlock(getGreatestCommonCondition(Conds)));
        VecInst = Builder.CreateSelect(getOrEmitMask(Conds, &VL),
                                       gatherOperandPack(IfTrue),
                                       gatherOperandPack(IfFalse));
        VecInst->setName(SomePhi->getName());
      } else {
        auto *PN = cast<PHINode>(*VP->elementValues().begin());
        auto *VecTy = getVectorType(*VP);
        auto *Alloca = new AllocaInst(VecTy, 0, PN->getName() + ".vector",
                                      &Entry->front());
        // Track the alloca so we can promote it back to phi later
        Allocas.push_back(Alloca);

        ArrayRef<const OperandPack *> OPs = VP->getOperandPacks();

        for (unsigned i = 0; i < PN->getNumIncomingValues(); i++) {
          auto *Cond = VL.getIncomingPhiCondition(PN, i);
          auto *BB = GetBlock(Cond);
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
        VecInst =
            VP->emitVectorLoad(Operands, getLoadStoreMask(Vals, &VL), Builder);
      else if (VP->isStore()) {
        VecInst =
            VP->emitVectorStore(Operands, getLoadStoreMask(Vals, &VL), Builder);
      } else
        VecInst = VP->emit(Operands, Builder);
    }

    // Conservatively extract all elements.
    // Let the later cleanup passes clean up dead extracts.
    if (!VP->isStore() && !VP->isReduction()) {
      if (auto *I = dyn_cast<Instruction>(VecInst)) {
        setInsertAtEndOfBlock(Builder, cast<Instruction>(VecInst)->getParent());
        for (auto &Item : enumerate(VP->getOrderedValues())) {
          if (auto *V = Item.value()) {
            unsigned i = Item.index();
            auto *Extract = Builder.CreateExtractElement(VecInst, i);
            ValueIndex[V] = {VP, i, Extract};
          }
        }
      } else {
        // It's possible that the ir builder constant-folds it into a constant
        auto *CV = cast<ConstantVector>(VecInst);
        for (auto &Item : enumerate(VP->getOrderedValues())) {
          if (auto *V = Item.value()) {
            unsigned i = Item.index();
            ValueIndex[V] = {VP, i, CV->getAggregateElement(i)};
          }
        }
      }
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

  BranchInst::Create(Latch, GetBlock(nullptr));
  Builder.SetInsertPoint(Latch);

  // Patch the mu nodes
  for (auto &Pair : MusToPatch) {
    PHINode *Mu = Pair.first;
    OperandPack &IterOP = Pair.second;
    Mu->setIncomingValue(1, gatherOperandPack(IterOP));
  }
  for (auto &Pair : ScalarMusToPatch)
    fixScalarUses(Pair.first);

  if (VL.getBackEdgeCond()) {
    Builder.CreateCondBr(getReifiedBackEdgeCond(&VL), Header, Exit);
  } else {
    Builder.CreateBr(Header);
    ReturnInst::Create(Ctx, Exit);
  }

  for (auto KV : VL.getGuardedLiveOuts())
    GuardedLiveOuts.insert(KV);

  return {Header, Exit};
}

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
  for (auto *PN : OneHotPhis)
    PN->dropAllReferences();
  for (auto *Mu : MuNodes)
    Mu->dropAllReferences();
  for (auto *I : Reifier.getInsertedInsts())
    if (!I->getParent())
      I->dropAllReferences();

  for (auto *BB : OldBlocks)
    BB->eraseFromParent();
  for (auto *PN : OneHotPhis)
    delete PN;
  for (auto *Mu : MuNodes)
    delete Mu;
  for (auto *I : Reifier.getInsertedInsts())
    if (!I->getParent())
      I->deleteValue();

  if (DumpAfterErasingOldBlocks)
    F->dump();

  // Restore SSA
  DominatorTree DT(*F);
  PromoteMemToReg(Allocas, DT);
  fixDefUseDominance(F, DT);

#if 0
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
#endif
}

namespace {
using CondVector = SmallVector<const ControlCondition *, 8>;
struct CondVectorInfo {
  using VecAndLoop = const std::pair<CondVector, VLoop *>;
  static VecAndLoop getEmptyKey() { return {{}, nullptr}; }

  static VecAndLoop getTombstoneKey() {
    return {{}, reinterpret_cast<VLoop *>(-1)};
  };

  static unsigned getHashValue(VecAndLoop &X) {
    return hash_combine(hash_combine_range(X.first.begin(), X.first.end()),
                        DenseMapInfo<VLoop *>::getHashValue(X.second));
  }

  static bool isEqual(const VecAndLoop &A, const VecAndLoop &B) {
    return A.second == B.second && A.first == B.first;
  }
};

} // namespace

static void collectMasks(SmallVectorImpl<const OperandPack *> &Masks,
                         ArrayRef<const VectorPack *> Packs,
                         ControlReifier &Reifier, Packer &Pkr) {
  DenseSet<std::pair<CondVector, VLoop *>, CondVectorInfo> Processed;
  auto *VPCtx = Pkr.getContext();

  auto ProcessConds = [&](CondVector Conds, VLoop *VL) {
    if (!Processed.insert({Conds, VL}).second)
      return;
    OperandPack OP;
    for (auto *C : Conds)
      OP.push_back(Reifier.getValue(C, VL));
    Masks.push_back(VPCtx->getCanonicalOperandPack(OP));
  };

  for (auto *VP : Packs) {
    auto Vals = VP->getOrderedValues();
    auto *I = cast<Instruction>(Vals.front());
    auto *VL = Pkr.getVLoopFor(I);
    if (VP->isLoad() || VP->isStore()) {
      CondVector Conds;
      getLoadStoreConds(Conds, Vals, VL);
      // Don't need masking if the pack has uniform conditions
      if (is_splat(Conds))
        continue;
      ProcessConds(Conds, VL);
    } else if (VP->isGamma()) {
      ArrayRef<const GammaNode *> Gammas = VP->getGammas();
      unsigned NumIncomings = Gammas.front()->PN->getNumIncomingValues();
      assert(all_of(Gammas, [&](auto *G2) {
        return G2->PN->getNumIncomingValues() == NumIncomings;
      }));
      for (unsigned i = 0; i < NumIncomings; i++) {
        CondVector Conds;
        for (auto *G : Gammas)
          Conds.push_back(VL->getIncomingPhiCondition(G->PN, i));
        ProcessConds(Conds, VL);
      }
    } else if (VP->isPHI() && VL->getOneHotPhi(cast<PHINode>(I))) {
      assert(false);
    }
  }
}

void VectorPackSet::codegen(IntrinsicBuilder &Builder, Packer &Pkr) {
 if (AllPacks.empty() && !TestCodeGen)
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
  Pkr.getVLoopInfo().doCoiteration(Builder.getContext(), *Pkr.getContext(),
                                   Pkr.getDA(), Pkr.getCDA());

  // Reify control conditions into boolean ir values
  ControlReifier Reifier(Builder.getContext(), Pkr.getDA());
  auto &LI = Pkr.getLoopInfo();
  auto &VLI = Pkr.getVLoopInfo();
  Reifier.reifyConditionsInLoop(&Pkr.getTopVLoop());
  for (auto *L : LI.getLoopsInPreorder())
    Reifier.reifyConditionsInLoop(VLI.getVLoop(L));

  // The reifier just inserted some new instructions,
  // run the pattern matcher on them.
  Pkr.matchSecondaryInsts(Reifier.getInsertedInsts());

  // Figure out the masks we need for predicated execution
  SmallVector<const OperandPack *> Seeds;
  collectMasks(Seeds, AllPacks, Reifier, Pkr);
  auto *VPCtx = Pkr.getContext();
  for (auto *VP : AllPacks) {
    auto Vals = VP->getOrderedValues();
    auto *I = cast<Instruction>(Vals.front());
    auto *VL = Pkr.getVLoopFor(I);
    auto &Guarded = VL->getGuardedLiveOuts();
    if (!Guarded.count(I))
      continue;
    OperandPack OP;
    for (auto *V : Vals) {
      auto *I = cast<Instruction>(V);
      assert(Guarded.count(I));
      assert(VL->getOneHotPhi(cast<PHINode>(Guarded.lookup(I))));
      OP.push_back(Guarded.lookup(I));
    }
    Seeds.push_back(VPCtx->getCanonicalOperandPack(OP));
  }

  // When running the bottom-up heuristic and encountering a pack of one hot
  // phis, also pack their reified conditions.
  auto GetExtraOperands = [&](const VectorPack *VP,
                              SmallVectorImpl<const OperandPack *> &ExtraOPs) {
    if (!VP->isPHI())
      return;
    auto Vals = VP->getOrderedValues();
    auto *PN = cast<PHINode>(Vals.front());
    if (!PN)
      return;
    auto *VL = Pkr.getVLoopFor(PN);
    if (!VL->getOneHotPhi(PN))
      return;
    OperandPack OP;
    for (auto *V : Vals)
      OP.push_back(Reifier.getValue(VL->getOneHotPhi(cast<PHINode>(V))->C, VL));
    ExtraOPs.push_back(VPCtx->getCanonicalOperandPack(OP));
  };

  // Do secondary packing
  Heuristic H(&Pkr, nullptr);
  Plan P(&Pkr);
  for (auto *VP : AllPacks)
    P.add(VP);
  for (auto *OP : Seeds)
    runBottomUpFromOperand(OP, P, H, false /*don't override existing packs*/,
                           GetExtraOperands);
  for (auto *VP : P)
    tryAdd(VP);

  // Look of consecutive loads/stores and speculatively compute their pointers if necessary
  for (auto *VP : AllPacks) {
    auto *Addr = VP->getLoadStorePointer();
    if (!Addr)
      continue;
    auto *AddrComp = dyn_cast<Instruction>(Addr);
    if (!AddrComp)
      continue;
    SmallVector<Instruction *> Insts;
    for (auto *V : VP->elementValues())
      Insts.push_back(cast<Instruction>(V));
    auto *C = Pkr.findSpeculationCond(AddrComp, Insts);
    auto *VL = Pkr.getVLoopFor(AddrComp);
    if (!isImplied(VL->getInstCond(AddrComp), C))
      VL->setInstCond(AddrComp, C);
  }

  // Lower everything
  VectorCodeGen CodeGen(Pkr, Builder, Reifier, ValueToPackMap);
  CodeGen.run();
}
