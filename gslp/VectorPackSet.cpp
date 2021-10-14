#include "VectorPackSet.h"
#include "BlockBuilder.h"
#include "CodeMotionUtil.h"
#include "ControlDependence.h"
#include "Packer.h"
#include "llvm/ADT/EquivalenceClasses.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Transforms/Utils/PromoteMemToReg.h"

using namespace llvm;

// Get the vector value representing `OP'.
// If `OP` is not directly produced by another Pack,
// we need to emit code to either swizzle it together.
static Value *gatherOperandPack(const OperandPack &OP,
                                const ValueIndexTy &ValueIndex,
                                const PackToValueTy &MaterializedPacks,
                                IRBuilderBase &Builder) {
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
      SrcScalars[V].push_back(i);
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

  Value *Acc;
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

  return Acc;
}

static Value *getOrEmitConditionPack(
    const ConditionPack *CP, const ValueIndexTy &ValueIndex,
    const PackToValueTy &MaterializedPacks,
    DenseMap<const ConditionPack *, Value *> &MaterializedCondPacks,
    IRBuilderBase &Builder) {
  if (auto *V = MaterializedCondPacks.lookup(CP))
    return V;

  if (CP->Kind == ConditionPack::CP_And) {
    assert(CP->OP);
    Value *Cond =
        gatherOperandPack(*CP->OP, ValueIndex, MaterializedPacks, Builder);
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
    auto *ParentCond =
        getOrEmitConditionPack(CP->Parent, ValueIndex, MaterializedPacks,
                               MaterializedCondPacks, Builder);
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

// Topsort the instructions s.t. instructions in the same packs are grouped
// together.
static std::vector<Instruction *>
schedule(Function *F, ArrayRef<const VectorPack *> Packs, Packer &Pkr) {
  auto &DA = Pkr.getDA();
  if (Packs.empty())
    return {};

  // Mapping values to where they are packed
  DenseMap<Value *, const VectorPack *> ValueToPackMap;
  for (auto *VP : Packs)
    for (Value *V : VP->elementValues())
      ValueToPackMap[V] = VP;

  // Schedule the instruction to the pack dependence.
  // In particular, we want the instructions to be packed stay together.
  const VectorPackContext *VPCtx = Packs[0]->getContext();
  using SchedulerItem =
      PointerUnion<Instruction *, const VectorPack *, const ControlCondition *>;
  DenseSet<void *> Reordered;
  std::vector<Instruction *> ReorderedInsts;
  std::function<void(SchedulerItem)> Schedule = [&](SchedulerItem Item) {
    bool Inserted = Reordered.insert(Item.getOpaqueValue()).second;
    if (!Inserted)
      return;

    auto *I = Item.dyn_cast<Instruction *>();
    auto *VP = Item.dyn_cast<const VectorPack *>();

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
    if (I && ValueToPackMap.count(I)) {
      Schedule(ValueToPackMap[const_cast<Instruction *>(I)]);
      return;
    }

    // Figure out the dependence
    std::vector<Value *> DependedValues;
    if (I) {
      // Make sure the control conditions are scheduled before the instruction
      Schedule(Pkr.getBlockCondition(I->getParent()));
      auto Depended = DA.getDepended(const_cast<Instruction *>(I));
      for (auto *V : VPCtx->iter_values(Depended))
        DependedValues.push_back(V);
    } else {
      assert(VP);
      // Make sure the control conditions are scheduled before the pack
      for (auto *V : VP->elementValues())
        Schedule(Pkr.getBlockCondition(cast<Instruction>(V)->getParent()));
      for (auto *V : VP->dependedValues())
        DependedValues.push_back(V);
    }

    // Recurse on the depended values
    for (auto *V : DependedValues)
      if (auto *I = dyn_cast<Instruction>(V))
        Schedule(I);

#ifndef NDEBUG
    for (auto *V : DependedValues)
      if (auto *I2 = dyn_cast<Instruction>(V))
        assert(std::count(ReorderedInsts.begin(), ReorderedInsts.end(), I2));
#endif

    // Now finalize ordering of this (pack of) instruction(s)
    if (I) {
      ReorderedInsts.push_back(I);
      return;
    }

    assert(VP);
    for (auto *V : VP->getOrderedValues())
      if (auto *I = dyn_cast_or_null<Instruction>(V))
        ReorderedInsts.push_back(I);
  };

  ReversePostOrderTraversal<Function *> RPO(F);
  // Schedule in RPO so that we can order return instructions properly
  for (auto *BB : RPO) {
    for (auto &I : *BB) {
      // Ignore branches, which we will generate from
      // scratch according to control-dep
      if (isa<ReturnInst>(&I) || !I.isTerminator())
        Schedule(&I);
    }
  }

  for (auto *VP : Packs)
    Schedule(VP);

  return ReorderedInsts;
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

void VectorPackSet::codegen(IntrinsicBuilder &Builder, Packer &Pkr) {
  ValueIndexTy ValueIndex;
  PackToValueTy MaterializedPacks;
  DenseMap<const ConditionPack *, Value *> MaterializedCondPacks;

  auto *VPCtx = Pkr.getContext();

  auto GetLoadStoreMask = [&](ArrayRef<Value *> Vals) -> Value * {
    SmallVector<const ControlCondition *> Conds;
    for (auto *V : Vals)
      Conds.push_back(Pkr.getBlockCondition(cast<Instruction>(V)->getParent()));
    auto *CP = VPCtx->getConditionPack(Conds);
    // nullptr means it's all true
    if (!CP)
      return nullptr;
    return getOrEmitConditionPack(CP, ValueIndex, MaterializedPacks,
                                  MaterializedCondPacks, Builder);
  };

  // Schedule the instructions
  std::vector<Instruction *> OrderedInsts = schedule(F, AllPacks, Pkr);

  // Remove the basic blocks from F
  std::vector<BasicBlock *> OldBlocks;
  for (auto &BB : *F)
    OldBlocks.push_back(&BB);

  auto &Ctx = F->getParent()->getContext();
  auto *Entry = BasicBlock::Create(Ctx, "entry", F);
  BlockBuilder BBuilder(Entry);

  // Instead of moving PHIs around,
  // we will demote them and implement control-flow join through memory
  DenseMap<PHINode *, AllocaInst *> DemotedPHIs;
  // Track the last used block for a given condition,
  // these are the blocks where we will store the incoming values to the demoted
  // allocas.
  SmallVector<AllocaInst *> Allocas;
  DenseMap<const ControlCondition *, BasicBlock *> LastBlockForCond;
  auto GetBlock = [&](const ControlCondition *C) {
    return LastBlockForCond[C] = BBuilder.getBlockFor(C);
  };
  auto GetLastBlockFor = [&](const ControlCondition *C) {
    if (auto *BB = LastBlockForCond.lookup(C))
      return BB;
    return GetBlock(C);
  };

  // Now generate code according to the schedule
  for (auto *I : OrderedInsts) {
    auto *Cond = Pkr.getBlockCondition(I->getParent());
    auto *VP = ValueToPackMap.lookup(I);

    // I is not packed
    if (!VP) {
      moveToEnd(I, GetBlock(Cond));
      continue;
    }

    // I is packed but we've already lowered that pack
    if (MaterializedPacks.count(VP))
      continue;

    // Get or create a new basic block to emit the pack
    SmallVector<const ControlCondition *, 8> Conds;
    for (auto *V : VP->elementValues())
      Conds.push_back(Pkr.getBlockCondition(cast<Instruction>(V)->getParent()));
    Builder.SetInsertPoint(GetBlock(getGreatestCommonCondition(Conds)));

    Value *VecInst;
    if (VP->isGamma()) {
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
        GateConds.push_back(getOrEmitConditionPack(
            CP, ValueIndex, MaterializedPacks, MaterializedCondPacks, Builder));
        GateVals.push_back(
            gatherOperandPack(Vals, ValueIndex, MaterializedPacks, Builder));
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
      auto *VecTy = getVectorType(*VP);
      auto *Alloca = new AllocaInst(VecTy, 0, "demoted", &Entry->front());
      // Track the alloca so we can promote it back to phi later
      Allocas.push_back(Alloca);
      auto *PN = cast<PHINode>(*VP->elementValues().begin());
      ArrayRef<const OperandPack *> OPs = VP->getOperandPacks();
      for (unsigned i = 0; i < PN->getNumIncomingValues(); i++) {
        IntrinsicBuilder::InsertPointGuard Guard(Builder);
        auto *Cond = Pkr.getEdgeCondition(PN->getIncomingBlock(i), PN->getParent());
        auto *BB = GetLastBlockFor(Cond);
        if (auto *Terminator = BB->getTerminator())
          Builder.SetInsertPoint(Terminator);
        else
          Builder.SetInsertPoint(BB);
        auto *Gathered = gatherOperandPack(*OPs[i], ValueIndex, MaterializedPacks, Builder);
        Builder.CreateStore(Gathered, Alloca);
      }
      VecInst = Builder.CreateLoad(VecTy, Alloca);
    } else {
      // For other instructions, we just get gather their operands and emit the
      // vector instruction Get the operands ready.
      SmallVector<Value *, 2> Operands;
      for (auto *OP : VP->getOperandPacks()) {
        Operands.push_back(
            gatherOperandPack(*OP, ValueIndex, MaterializedPacks, Builder));
      }

      // Now we can emit the vector instruction
      ArrayRef<Value *> Vals = VP->getOrderedValues();
      if (VP->isLoad())
        VecInst = VP->emitVectorLoad(Operands, GetLoadStoreMask(Vals), Builder);
      else if (VP->isStore())
        VecInst =
            VP->emitVectorStore(Operands, GetLoadStoreMask(Vals), Builder);
      else
        VecInst = VP->emit(Operands, Builder);
    }

    // Conservatively extract all elements.
    // Let the later cleanup passes clean up dead extracts.
    if (!VP->isStore() && !VP->isReduction()) {
      for (auto &Item : enumerate(VP->getOrderedValues())) {
        if (auto *V = Item.value()) {
          auto *Extract = Builder.CreateExtractElement(VecInst, Item.index());
          V->replaceAllUsesWith(Extract);
        }
      }
    }

    // Update the value index
    // to track where the originally scalar values are produced
    auto OutputLanes = VP->getOrderedValues();
    for (unsigned i = 0, e = OutputLanes.size(); i != e; i++)
      if (auto *V = OutputLanes[i])
        ValueIndex[V] = {VP, i};

    // Map the pack to its materialized value
    MaterializedPacks[VP] = VecInst;
  }

  for (auto *BB : OldBlocks)
    BB->eraseFromParent();

  DominatorTree DT(*F);
  PromoteMemToReg(Allocas, DT);

  // Another pass to delete trivially dead instructions
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

  errs() << *F << '\n';
}
