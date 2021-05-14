#include "VectorPackSet.h"
#include "LocalDependenceAnalysis.h"
#include "Packer.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"

using namespace llvm;

// Get the vector value representing `OpndPack'.
// If `OpndPack` is not directly produced by another Pack,
// we need to emit code to either swizzle it together.
Value *VectorPackSet::gatherOperandPack(const OperandPack &OpndPack,
                                        const ValueIndexTy &ValueIndex,
                                        const PackToValueTy &MaterializedPacks,
                                        IntrinsicBuilder &Builder) {
  struct GatherEdge {
    unsigned SrcIndex;
    unsigned DestIndex;
  };

  DenseMap<const VectorPack *, SmallVector<GatherEdge, 4>> SrcPacks;
  DenseMap<Value *, SmallVector<unsigned, 4>> SrcScalars;

  // Figure out sources of the values in `OpndPack`
  const unsigned NumValues = OpndPack.size();
  for (unsigned i = 0; i < NumValues; i++) {
    auto *V = OpndPack[i];
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
    // 2)uMerge the partial gathers
    BitVector DefinedBits = PartialGathers[0].DefinedBits;
    Acc = PartialGathers[0].Gather;
    for (auto &PG :
         make_range(PartialGathers.begin() + 1, PartialGathers.end())) {
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
    auto *VecTy = getVectorType(OpndPack);
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

void VectorPackSet::add(const VectorPack *VP) {
  auto *BB = VP->getBasicBlock();
  PackedValues[BB] |= VP->getElements();
  AllPacks.push_back(VP);

  for (Value *V : VP->elementValues())
    ValueToPackMap[V] = VP;
  Packs[BB].push_back(VP);

  NumPacks++;
}

bool VectorPackSet::isCompatibleWith(const VectorPack &VP) const {
  auto *BB = VP.getBasicBlock();
  // Abort if one of the value we want to produce is produced by another pack
  auto It = PackedValues.find(BB);
  if (It != PackedValues.end() && It->second.anyCommon(VP.getElements())) {
    return false;
  }

  SmallPtrSet<Value *, 8> NewValues;
  for (auto *V : VP.elementValues())
    if (V)
      NewValues.insert(V);

  // Do a DFS on the dependence graph starting from VP.
  // We want to see if we can get back to any of VP's values
  std::vector<const VectorPack *> Worklist{&VP};
  DenseSet<const VectorPack *> Visited;
  while (!Worklist.empty()) {
    auto *VP = Worklist.back();
    Worklist.pop_back();

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

void VectorPackSet::removeAux(const VectorPack *VP) {
  auto *BB = VP->getBasicBlock();
  PackedValues[BB] ^= VP->getElements();

  for (auto *V : VP->elementValues())
    ValueToPackMap.erase(V);
}

void VectorPackSet::pop() {
  auto &VP = AllPacks.back();
  auto *BB = VP->getBasicBlock();
  assert(Packs[BB].back() == VP);
  removeAux(VP);
  Packs[BB].pop_back();
  AllPacks.pop_back();
  NumPacks--;
}

static float getBlockWeight(BasicBlock *BB, BlockFrequencyInfo *BFI) {
  return 1.0;
  return float(BFI->getBlockFreq(BB).getFrequency()) /
         float(BFI->getEntryFreq());
}

static float getBlockWeight(const OperandPack &OpndPack,
                            BlockFrequencyInfo *BFI) {
  return 1.0;
  float weight = 0;
  for (auto *V : OpndPack)
    if (auto *I = dyn_cast<Instruction>(V))
      weight = std::max(weight, getBlockWeight(I->getParent(), BFI));
  return weight;
}

// FIXME: this is a mess
float VectorPackSet::getCostSaving(TargetTransformInfo *TTI,
                                   BlockFrequencyInfo *BFI) const {
  if (NumPacks == 0)
    return 0;

  int CostSaving = 0;
  assert(AllPacks.size() == NumPacks);
  // Compute arithmetic cost saving
  for (auto *VP : AllPacks) {
    auto *BB = VP->getBasicBlock();
    CostSaving += VP->getCost() * getBlockWeight(BB, BFI);
  }

  // Update cost to consider shuffles

  // FIXME: the code below accounts for most of the overhead...
  // First figure out which values are now in vectors
  ValueIndexTy ValueIndex;
  for (auto &VP : AllPacks) {
    unsigned i = 0;
    for (auto *V : VP->getOrderedValues())
      if (V)
        ValueIndex[V] = {VP, i++};
  }

  const int GatherCost = 2;

  // FIXME:
  // use of block frequency is pessimistic when we can hoist gathers out of
  // loops
  for (auto &VP : AllPacks) {
    auto *BB = VP->getBasicBlock();
    for (auto *OpndPack : VP->getOperandPacks()) {
      auto *VecTy = getVectorType(*OpndPack);

      // No cost for constant pack
      if (isConstantPack(*OpndPack))
        continue;

      // special case for broadcast
      if (is_splat(*OpndPack)) {
        float Weight =
            std::min(getBlockWeight(*OpndPack, BFI), getBlockWeight(BB, BFI));
        float SplatCost =
            TTI->getShuffleCost(TargetTransformInfo::SK_Broadcast, VecTy, 0);
        CostSaving += Weight * SplatCost;
        continue;
      }

      float BBCost = 0;
      // figure out from where we need to gather
      SmallPtrSet<const VectorPack *, 4> SrcPacks;
      unsigned LaneId = 0;
      for (Value *V : *OpndPack) {
        auto It = ValueIndex.find(V);
        if (It != ValueIndex.end()) {
          auto &VPIdx = It->second;
          SrcPacks.insert(VPIdx.VP);
        } else {
          BBCost += TTI->getVectorInstrCost(Instruction::InsertElement, VecTy,
                                            LaneId);
        }
        LaneId++;
      }

      if (SrcPacks.size() > 1) {
        BBCost += GatherCost * SrcPacks.size();
      } else if (!SrcPacks.empty()) {
        auto *SrcPack = *SrcPacks.begin();
        // We are selecting a subset of that pack
        if (SrcPack->getElements().count() != OpndPack->size()) {
          BBCost += GatherCost;
        } else {
          // Now see if we need to permute
          unsigned i = 0;
          bool InOrder = true;
          for (Value *V : *OpndPack) {
            auto It = ValueIndex.find(V);
            if (It == ValueIndex.end() || It->second.Idx != i) {
              InOrder = false;
              break;
            }
            i++;
          }
          if (!InOrder) {
            BBCost += TTI->getShuffleCost(
                TargetTransformInfo::SK_PermuteSingleSrc, VecTy);
          }
        }
      }
      CostSaving += BBCost * getBlockWeight(*OpndPack, BFI);
    }
  }

  // FIXME: this seems to be the bottleneck.  fix it.
  std::vector<VectorPackIndex> Extractions;
  Extractions.reserve(ValueIndex.size());
  // Now consider scalar use of vector output
  // FIXME: THIS DOES NOT WORK IN GENERAL... (e.g., FMA)
  // for (auto &I : make_range(inst_begin(F), inst_end(F))) {
  //  if (ValueIndex.count(&I))
  //    continue;
  //  for (Value *V : I.operands()) {
  //    auto It = ValueIndex.find(V);
  //    if (It != ValueIndex.end()) {
  //      Extractions.push_back(It->second);
  //    }
  //  }
  //}
  for (auto &ValueAndIdx : ValueIndex) {
    auto *V = ValueAndIdx.first;
    auto &VPIdx = ValueAndIdx.second;
    for (const User *U : V->users()) {
      if (!ValueIndex.count(U)) {
        Extractions.push_back(VPIdx);
        break;
      }
    }
  }

  std::stable_sort(Extractions.begin(), Extractions.end());

  VectorPackIndex *Prev = nullptr;

  for (auto &VPIdx : Extractions) {
    if (Prev && VPIdx == *Prev)
      continue;
    auto *BB = VPIdx.VP->getBasicBlock();
    auto *VecTy = getVectorType(*VPIdx.VP);
    float ExtractCost =
        TTI->getVectorInstrCost(Instruction::ExtractElement, VecTy, VPIdx.Idx);
    CostSaving += ExtractCost * getBlockWeight(BB, BFI);
    Prev = &VPIdx;
  }

  return CostSaving;
}

// Topsort the vector packs.
// Also reschedule the basic block according to the sorted packs.
//
// This reordering makes codegen easier because we can
// just insert the vector instruction immediately after the last
// instruction that you are replacing.
static std::vector<const VectorPack *>
sortPacksAndScheduleBB(BasicBlock *BB, ArrayRef<const VectorPack *> Packs,
                       LocalDependenceAnalysis &LDA) {
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
    for (Value *V : VP->dependedValues()) {
      auto It = ValueToPackMap.find(V);
      if (It != ValueToPackMap.end())
        SortPack(It->second);
    }

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
      auto Depended = LDA.getDepended(const_cast<Instruction *>(I));
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

// FIXME: maybe we need to do some LICM and CSE for these gathers??
// LOOK INTO SLP
void VectorPackSet::codegen(IntrinsicBuilder &Builder, Packer &Pkr) {
  ValueIndexTy ValueIndex;
  PackToValueTy MaterializedPacks;

  std::vector<Instruction *> DeadInsts;

  // Generate code in RPO of the CFG
  ReversePostOrderTraversal<Function *> RPO(F);
  for (BasicBlock *BB : RPO) {
    if (Packs[BB].empty())
      continue;

    // Determine the schedule according to the dependence constraint
    std::vector<const VectorPack *> OrderedPacks =
        sortPacksAndScheduleBB(BB, Packs[BB], Pkr.getLDA(BB));

    // Now generate code according to the schedule
    for (auto *VP : OrderedPacks) {
      // Get the operands ready.
      SmallVector<Value *, 2> Operands;
      unsigned OperandId = 0;
      for (auto *OpndPack : VP->getOperandPacks()) {
        VP->setOperandGatherPoint(OperandId, Builder);
        Operands.push_back(gatherOperandPack(*OpndPack, ValueIndex,
                                             MaterializedPacks, Builder));
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
      for (unsigned i = 0, e = OutputLanes.size(); i != e; i++) {
        if (auto *V = OutputLanes[i])
          ValueIndex[V] = {VP, i};
      }
      // Map the pack to its materialized value
      MaterializedPacks[VP] = VecInst;
    }
  }

  // Delete the dead instructions.
  // Do it the reverse of program order to avoid dangling pointer.
  for (auto *I : make_range(DeadInsts.rbegin(), DeadInsts.rend())) {
    auto *Undef = UndefValue::get(I->getType());
    I->replaceAllUsesWith(Undef);
    I->dropAllReferences();
  }
  for (auto *I : make_range(DeadInsts.rbegin(), DeadInsts.rend())) {
    assert(!I->isTerminator());
    I->eraseFromParent();
  }
}

void VectorPackSet::addScalar(Instruction *I, const VectorPackContext &VPCtx) {
  BasicBlock *BB = I->getParent();
  assert(!PackedValues[BB].test(VPCtx.getScalarId(I)) &&
         "trying to add an already packed value");
  PackedValues[BB].set(VPCtx.getScalarId(I));
}

bool VectorPackSet::contains(Instruction *I,
                             const VectorPackContext &VPCtx) const {
  BasicBlock *BB = I->getParent();
  auto It = PackedValues.find(BB);
  return It != PackedValues.end() && It->second.test(VPCtx.getScalarId(I));
}
