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

using namespace llvm;

// Get the vector value representing `OP'.
// If `OP` is not directly produced by another Pack,
// we need to emit code to either swizzle it together.
Value *VectorPackSet::gatherOperandPack(const OperandPack &OP,
                                        const ValueIndexTy &ValueIndex,
                                        const PackToValueTy &MaterializedPacks,
                                        IntrinsicBuilder &Builder) {
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

static BasicBlock *getBlockForPack(const VectorPack *VP) {
  for (auto *V : VP->elementValues())
    if (auto *I = dyn_cast<Instruction>(V))
      return I->getParent();
  llvm_unreachable("not block for pack");
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
static std::vector<Instruction *> schedule(Function *F,
                                           ArrayRef<const VectorPack *> Packs,
                                           GlobalDependenceAnalysis &DA) {
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
  using InstOrPack = PointerUnion<Instruction *, const VectorPack *>;
  DenseSet<void *> Reordered;
  std::vector<Instruction *> ReorderedInsts;
  std::function<void(InstOrPack)> Schedule = [&](InstOrPack IOP) {
    bool Inserted = Reordered.insert(IOP.getOpaqueValue()).second;
    if (!Inserted)
      return;

    auto *I = IOP.dyn_cast<Instruction *>();
    auto *VP = IOP.dyn_cast<const VectorPack *>();

    if (I && !VPCtx->isKnownValue(I)) {
      // If this is an unknown instruction,
      // we must just inserted it for packed PHIs.
      // Don't even bother with checking dependence,
      // because these instructions are right before the terminator.
      assert(isa<ShuffleVectorInst>(I) || isa<InsertElementInst>(I) ||
             isa<BranchInst>(I));
      assert(!ValueToPackMap.count(I));
      ReorderedInsts.push_back(I);
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
      auto Depended = DA.getDepended(const_cast<Instruction *>(I));
      for (auto *V : VPCtx->iter_values(Depended))
        DependedValues.push_back(V);
    } else {
      assert(VP);
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

  for (auto &I : instructions(F)) {
    // Ignore branches which we will generate from
    // scratch according to control-dep
    if (!I.isTerminator())
      Schedule(&I);
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

  errs() << "!!! packs <<<\n";
  for (auto *VP : AllPacks)
    errs() << *VP << '\n';
  errs() << ">>>>>\n";
  abort();

  auto &LI = Pkr.getLoopInfo();
  auto *TTI = Pkr.getTTI();

  // Schedule the instructions
  std::vector<Instruction *> OrderedInsts = schedule(F, AllPacks, Pkr.getDA());

  // Remove the basic blocks from F
  std::vector<BasicBlock *> OldBlocks;
  for (auto &BB : *F) {
    OldBlocks.push_back(&BB);
    BB.removeFromParent();
  }

  // Now generate code according to the schedule
  auto &Ctx = F->getParent()->getContext();
  BlockBuilder BBuilder(BasicBlock::Create(Ctx, "entry", F));
  for (auto *I : OrderedInsts) {
    auto *Cond = Pkr.getBlockCondition(I->getParent());
    auto *VP = ValueToPackMap.lookup(I);

    // I is not packed
    if (!VP) {
      moveToEnd(I, BBuilder.getBlockFor(Cond));
      continue;
    }

    // I is packed but we've already lowered that pack
    if (MaterializedPacks.count(VP))
      continue;

    // Get the operands ready.
    SmallVector<Value *, 2> Operands;
    for (auto &Item : enumerate(VP->getOperandPacks())) {
      auto *OP = Item.value();
      VP->setOperandGatherPoint(Item.index(), Builder);
      Operands.push_back(
          gatherOperandPack(*OP, ValueIndex, MaterializedPacks, Builder));
    }

    // Get or create a new basic block to emit the pack
    SmallVector<const ControlCondition *, 8> Conds;
    for (auto *V : VP->elementValues())
      Conds.push_back(
          Pkr.getBlockCondition(cast<Instruction>(V)->getParent()));
    Builder.SetInsertPoint(
        BBuilder.getBlockFor(getGreatestCommonCondition(Conds)));

    // Now we can emit the vector instruction
    auto *VecInst = VP->emit(Operands, Builder);

    // Conservatively extract all elements.
    // Let the later cleanup passes clean up dead extracts.
    if (!isa<StoreInst>(VecInst) && !VP->isReduction()) {
      for (auto &Item : enumerate(VP->getOrderedValues())) {
        if (auto *V = Item.value()) {
          auto *Extract = Builder.CreateExtractElement(VecInst, Item.index());
          V->replaceAllUsesWith(Extract);
        }
      }
    }
  }

#if 0
    for (auto *VP : OrderedPacks) {
      if (VP->isPHI())
        PHIPacks.push_back(VP);
      // Delay emitting reduction until later
      if (VP->isReduction()) {
        auto *L = LI.getLoopFor(BB);
        assert(L->getLoopLatch());
        RdxPacks[L->getLoopLatch()].push_back(VP);
        continue;
      }
      // Get the operands ready.
      SmallVector<Value *, 2> Operands;
      unsigned OperandId = 0;
      for (auto *OP : VP->getOperandPacks()) {
        VP->setOperandGatherPoint(OperandId, Builder);
        Value *Gathered;
        // Just pass in undef for PHI nodes, we will patch them up later
        if (VP->isPHI())
          Gathered = UndefValue::get(getVectorType(*OP));
        else
          Gathered =
              gatherOperandPack(*OP, ValueIndex, MaterializedPacks, Builder);
        Operands.push_back(Gathered);
        OperandId++;
      }

      Instruction *PackLeader = nullptr;
      for (auto *V : VP->elementValues())
        if (auto *I = dyn_cast<Instruction>(V)) {
          PackLeader = I;
          break;
        }
      assert(PackLeader);
      Builder.SetInsertPoint(PackLeader);

      // Now we can emit the vector instruction
      auto *VecInst = VP->emit(Operands, Builder);

      // Conservatively extract all elements.
      // Let the later cleanup passes clean up dead extracts.
      if (!isa<StoreInst>(VecInst) && !VP->isReduction()) {
        unsigned LaneId = 0;
        if (isa<PHINode>(VecInst))
          Builder.SetInsertPoint(BB->getFirstNonPHI());
        auto OutputLanes = VP->getOrderedValues();
        for (unsigned i = 0, e = OutputLanes.size(); i != e; i++) {
          if (auto *V = OutputLanes[i]) {
            auto *Extract = Builder.CreateExtractElement(VecInst, i);
            V->replaceAllUsesWith(Extract);
          }
        }
      }

      // Mark the packed values as dead so we can delete them later
      for (auto *V : VP->elementValues()) {
        if (auto *I = dyn_cast<Instruction>(V))
          DeadInsts.push_back(I);
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
#endif
}
