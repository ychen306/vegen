#include "VectorPackSet.h"
#include "Packer.h"
#include "CodeMotionUtil.h"
#include "llvm/ADT/EquivalenceClasses.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Transforms/Utils/Local.h"

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

// Topsort the vector packs.
// Also reschedule the basic block according to the sorted packs.
//
// This reordering makes codegen easier because we can
// just insert the vector instruction immediately after the last
// instruction that you are replacing.
static std::vector<const VectorPack *>
sortPacksAndScheduleBB(BasicBlock *BB, ArrayRef<const VectorPack *> Packs,
                       GlobalDependenceAnalysis &DA) {
  if (Packs.empty())
    return std::vector<const VectorPack *>();

  // Mapping values to where they are packed
  DenseMap<Value *, const VectorPack *> ValueToPackMap;
  for (auto *VP : Packs) {
    for (Value *V : VP->elementValues())
      ValueToPackMap[V] = VP;
  }

  // Sort the packs by dependence
  std::vector<const VectorPack *> SortedPacks;
  DenseSet<const VectorPack *> Visited;
  std::function<void(const VectorPack *)> SortPack = [&](const VectorPack *VP) {
    bool Inserted = Visited.insert(VP).second;
    if (!Inserted)
      return;

    // visit the depended packs
    for (Value *V : VP->dependedValues())
      if (auto *DependedVP = ValueToPackMap.lookup(V))
        SortPack(DependedVP);

    SortedPacks.push_back(VP);
  };

  // Schedule the basic block subject to the pack dependence.
  // In particular, we want the instructions to be packed stay together.
  const VectorPackContext *VPCtx = Packs[0]->getContext();
  using InstOrPack = PointerUnion<const Instruction *, const VectorPack *>;
  DenseSet<void *> Reordered;
  std::vector<const Instruction *> ReorderedInsts;
  std::function<void(InstOrPack)> Schedule = [&](InstOrPack IOP) {
    bool Inserted = Reordered.insert(IOP.getOpaqueValue()).second;
    if (!Inserted)
      return;

    auto *I = IOP.dyn_cast<const Instruction *>();
    auto *VP = IOP.dyn_cast<const VectorPack *>();

    if (I && !VPCtx->isKnownValue(I)) {
      // If this is an unknown instruction,
      // we must just inserted it for packed PHIs.
      // Don't even bother with checking dependence,
      // because these instructions are right before the terminator.
      assert(isa<ShuffleVectorInst>(I) || isa<InsertElementInst>(I));
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
    for (auto *V : DependedValues) {
      if (auto *I = dyn_cast<Instruction>(V)) {
        if (I->getParent() == BB) {
          Schedule(I);
        }
      }
    }

#ifndef NDEBUG
    for (auto *V : DependedValues) {
      if (auto *I2 = dyn_cast<Instruction>(V)) {
        if (I2->getParent() == BB) {
          assert(std::count(ReorderedInsts.begin(), ReorderedInsts.end(), I2));
        }
      }
    }
#endif

    // Now finalize ordering of this (pack of) instruction(s)
    if (I) {
      ReorderedInsts.push_back(I);
    } else {
      assert(VP);
      for (auto *V : VP->getOrderedValues()) {
        if (V)
          if (auto *I = dyn_cast<Instruction>(V))
            ReorderedInsts.push_back(I);
      }
    }
  };

  // Sort the packs first
  for (auto *VP : Packs)
    SortPack(VP);
  assert(SortedPacks.size() == Packs.size());

  for (auto &I : *BB)
    Schedule(&I);
  for (auto *VP : Packs)
    Schedule(VP);

  assert(ReorderedInsts.size() == BB->size());
  assert((*ReorderedInsts.rbegin())->isTerminator());

  // Reorder the instruction according to the schedule
  for (auto *I : ReorderedInsts)
    const_cast<Instruction *>(I)->removeFromParent();
  assert(BB->empty());
  auto &InstList = BB->getInstList();
  for (auto *I : ReorderedInsts)
    InstList.push_back(const_cast<Instruction *>(I));
  assert(BB->size() == ReorderedInsts.size());

  return SortedPacks;
}

void VectorPackSet::codegen(IntrinsicBuilder &Builder, Packer &Pkr) {
  ValueIndexTy ValueIndex;
  PackToValueTy MaterializedPacks;

  // Move instructions that we want to pack together into the same basic block
  EquivalenceClasses<Instruction *> EC;
  for (auto *VP : AllPacks) {
    Instruction *Leader = nullptr;
    for (auto *V : VP->elementValues())
      if (auto *I = dyn_cast<Instruction>(V)) {
        if (!Leader) {
          Leader = I;
          continue;
        }
        EC.unionSets(Leader, I);
      }
  }
  gatherInstructions(F, EC, Pkr.getLoopInfo(), Pkr.getDT(), Pkr.getPDT(),
                     Pkr.getSE(), Pkr.getLDA());

  std::vector<Instruction *> DeadInsts;

  std::map<BasicBlock *, SmallVector<const VectorPack *>> PacksByBlock;
  for (auto *VP : AllPacks)
    PacksByBlock[getBlockForPack(VP)].push_back(VP);

  // Generate code in RPO of the CFG
  ReversePostOrderTraversal<Function *> RPO(F);
  SmallVector<const VectorPack *> PHIPacks;
  for (BasicBlock *BB : RPO) {
    if (!PacksByBlock.count(BB))
      continue;

    // Determine the schedule according to the dependence constraint
    std::vector<const VectorPack *> OrderedPacks =
        sortPacksAndScheduleBB(BB, PacksByBlock[BB], Pkr.getDA());

    // Now generate code according to the schedule
    for (auto *VP : OrderedPacks) {
      if (VP->isPHI())
        PHIPacks.push_back(VP);
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
      if (!isa<StoreInst>(VecInst)) {
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
  }

  // Patch up the operands of the phi packs
  for (auto *VP : PHIPacks) {
    ArrayRef<OperandPack *> OPs = VP->getOperandPacks();
    for (unsigned i = 0; i < OPs.size(); i++) {
      Value *Gathered =
          gatherOperandPack(*OPs[i], ValueIndex, MaterializedPacks, Builder);
      cast<Instruction>(MaterializedPacks[VP])->setOperand(i, Gathered);
    }
  }

  // Delete the dead instructions.
  // Do it the reverse of program order to avoid dangling pointer.
  for (Instruction *I : reverse(DeadInsts)) {
    auto *Undef = UndefValue::get(I->getType());
    I->replaceAllUsesWith(Undef);
    I->dropAllReferences();
  }
  for (Instruction *I : reverse(DeadInsts)) {
    assert(!I->isTerminator());
    I->eraseFromParent();
  }

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
}
