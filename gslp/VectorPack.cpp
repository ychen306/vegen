#include "VectorPack.h"
#include "ControlDependence.h"
#include "MatchManager.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/Analysis/VectorUtils.h"

using namespace llvm;

// FIXME: we need to generalize the definition of an operand pack
// because some of the input lanes are "DONT CARES" (e.g. _mm_div_pd)
std::vector<OperandPack> VectorPack::computeOperandPacksForGeneral() {
  auto &Sig = Producer->getSignature();
  unsigned NumInputs = Sig.numInputs();
  auto LaneOps = Producer->getLaneOps();
  unsigned NumLanes = LaneOps.size();
  std::vector<OperandPack> OperandPacks(NumInputs);

  struct BoundInput {
    InputSlice Slice;
    Value *V;
    // Order by offset of the slice
    bool operator<(const BoundInput &Other) const {
      return Slice < Other.Slice;
    }
  };

  // Figure out which input packs we need
  for (unsigned i = 0; i < NumInputs; i++) {
    std::vector<BoundInput> InputValues;
    // Size of one element in this input vector
    unsigned ElementSize = 0;
    // Find output lanes that uses input `i` and record those uses
    for (unsigned j = 0; j < NumLanes; j++) {
      ArrayRef<InputSlice> BoundSlices = LaneOps[j].getBoundSlices();
      for (unsigned k = 0; k < BoundSlices.size(); k++) {
        auto &BS = BoundSlices[k];
        if (BS.InputId != i)
          continue;
        ElementSize = BS.size();
        InputValues.push_back(
            {BS, Matches[j] ? Matches[j]->Inputs[k] : nullptr});
      }
    }
    assert(ElementSize != 0);

    // Sort the input values by their slice offset
    std::sort(InputValues.begin(), InputValues.end());

    unsigned CurOffset = 0;
    unsigned Stride = InputValues[0].Slice.size();
    auto &OP = OperandPacks[i];
    for (const BoundInput &BV : InputValues) {
      while (CurOffset < BV.Slice.Lo) {
        OP.push_back(nullptr);
        CurOffset += Stride;
      }
      assert(CurOffset == BV.Slice.Lo);
      OP.push_back(BV.V);
      CurOffset += Stride;
    }
    unsigned InputSize = Sig.InputBitwidths[i];
    while (CurOffset < InputSize) {
      OP.push_back(nullptr);
      CurOffset += Stride;
    }
    assert(OP.size() * Stride == InputSize);

    // Compute the type of don't care vector as special cases
    if (!OP.front() && is_splat(OP)) {
      OP.Ty = FixedVectorType::get(
          IntegerType::get(VPCtx->getFunction()->getContext(), ElementSize),
          OP.size());
    }
  }

  return OperandPacks;
}

static void
getOperandPacksFromCondition(const ConditionPack *CP,
                             SmallVectorImpl<const OperandPack *> &OPs) {
  if (!CP)
    return;

  if (CP->Parent) {
    getOperandPacksFromCondition(CP->Parent, OPs);
  } else {
    for (auto *CP2 : CP->CPs)
      getOperandPacksFromCondition(CP2, OPs);
  }

  if (CP->OP)
    OPs.push_back(CP->OP);
}

std::vector<OperandPack> VectorPack::computeOperandPacksForLoad() {
  if (!IsGatherScatter) {
    // Only need the single *scalar* pointer, doesn't need packed operand
    return {};
  }

  OperandPack OP;
  for (auto *L : Loads)
    OP.push_back(L->getPointerOperand());
  return {OP};
}

std::vector<OperandPack> VectorPack::computeOperandPacksForStore() {
  OperandPack ValueOP;
  for (auto *S : Stores)
    ValueOP.push_back(S->getValueOperand());

  if (!IsGatherScatter)
    return {ValueOP};

  OperandPack PtrOP;
  for (auto *S : Stores)
    PtrOP.push_back(S->getPointerOperand());
  return {PtrOP, ValueOP};
}

std::vector<OperandPack> VectorPack::computeOperandPacksForPhi() {
  auto *FirstPHI = PHIs[0];
  unsigned NumIncomings = FirstPHI->getNumIncomingValues();
  // We need as many packs as there are incoming edges
  std::vector<OperandPack> OperandPacks(NumIncomings);
  for (unsigned i = 0; i < NumIncomings; i++)
    // FIXME: make sure that PH->getIncomingBlock(i) is control-equivalent to
    // FirstPHI->getIncomingBlock(i)
    for (auto *PH : PHIs)
      OperandPacks[i].push_back(PH->getIncomingValue(i));
  return OperandPacks;
}

static Type *getScalarTy(ArrayRef<const Operation::Match *> Matches) {
  for (auto &M : Matches)
    if (M)
      return M->Output->getType();
  llvm_unreachable("Matches can't be all null");
  return nullptr;
}

Value *VectorPack::emitVectorGeneral(ArrayRef<Value *> Operands,
                                     IntrinsicBuilder &Builder) const {
  auto *VecInst = Producer->emit(Operands, Builder);
  // Fix the output type
  auto *VecType = FixedVectorType::get(getScalarTy(Matches), Matches.size());
  return Builder.CreateBitCast(VecInst, VecType);
}

namespace {
template <typename LoadStores> Align getCommonAlignment(LoadStores Insts) {
  Align A = Insts.front()->getAlign();
  for (auto *I : drop_begin(Insts))
    A = std::min(A, I->getAlign());
  return A;
}
} // namespace

Value *VectorPack::emitVectorLoad(ArrayRef<Value *> Operands, Value *Mask,
                                  IntrinsicBuilder &Builder) const {
  auto *FirstLoad = Loads[0];
  auto &DL = FirstLoad->getParent()->getModule()->getDataLayout();
  auto *ScalarLoadTy = FirstLoad->getType();

  // Figure out type of the vector that we are loading
  auto *ScalarPtr = FirstLoad->getPointerOperand();
  auto *ScalarTy = cast<PointerType>(ScalarPtr->getType())->getElementType();
  auto *VecTy = FixedVectorType::get(ScalarTy, Loads.size());

  // Cast the scalar pointer to a vector pointer
  unsigned AS = FirstLoad->getPointerAddressSpace();
  Value *VecPtr = Builder.CreateBitCast(ScalarPtr, VecTy->getPointerTo(AS));

  // Emit the load
  Instruction *VecLoad;
  if (IsGatherScatter)
    VecLoad = Builder.CreateMaskedGather(Operands.front(),
                                         getCommonAlignment(Loads), Mask);
  else if (Mask)
    VecLoad = Builder.CreateMaskedLoad(VecPtr, FirstLoad->getAlign(), Mask);
  else
    VecLoad = Builder.CreateAlignedLoad(VecTy, VecPtr, FirstLoad->getAlign());

  std::vector<Value *> Values;
  for (auto *LI : Loads)
    if (LI)
      Values.push_back(LI);
  return propagateMetadata(VecLoad, Values);
}

Value *VectorPack::emitVectorStore(ArrayRef<Value *> Operands, Value *Mask,
                                   IntrinsicBuilder &Builder) const {
  // Emit the vector store
  Instruction *VecStore;
  if (IsGatherScatter) {
    auto *Ptrs = Operands[0];
    auto *Values = Operands[1];
    VecStore = Builder.CreateMaskedScatter(Values, Ptrs,
                                           getCommonAlignment(Stores), Mask);
  } else {
    Value *VecValue = Operands.front();
    auto *FirstStore = Stores.front();

    // Figure out the store alignment
    unsigned Alignment = FirstStore->getAlignment();
    unsigned AS = FirstStore->getPointerAddressSpace();
    auto &DL = FirstStore->getParent()->getModule()->getDataLayout();
    if (!Alignment)
      Alignment =
          DL.getABITypeAlignment(FirstStore->getValueOperand()->getType());

    // Cast the scalar pointer to vector pointer
    Value *ScalarPtr = FirstStore->getPointerOperand();
    Value *VecPtr =
        Builder.CreateBitCast(ScalarPtr, VecValue->getType()->getPointerTo(AS));

    if (!Mask)
      VecStore = Builder.CreateAlignedStore(VecValue, VecPtr, Align(Alignment));
    else
      VecStore =
          Builder.CreateMaskedStore(VecValue, VecPtr, Align(Alignment), Mask);
  }

  SmallVector<Value *, 4> Stores_(Stores.begin(), Stores.end());
  return propagateMetadata(VecStore, Stores_);
}

static void getGEPOperands(unsigned i, ArrayRef<GetElementPtrInst *> GEPs,
                           SmallVectorImpl<Value *> &Operands) {
  for (auto *GEP : GEPs)
    Operands.push_back(GEP->getOperand(i));
}

void VectorPack::computeOperandPacks() {
  switch (Kind) {
  case General:
    canonicalizeOperandPacks(computeOperandPacksForGeneral());
    break;
  case Load:
    canonicalizeOperandPacks(computeOperandPacksForLoad());
    break;
  case Store:
    canonicalizeOperandPacks(computeOperandPacksForStore());
    break;
  case Phi:
    canonicalizeOperandPacks(computeOperandPacksForPhi());
    break;
  case Reduction: {
    SmallVector<OperandPack, 4> OPs;
    assert(Rdx->Elts.size() % RdxLen == 0);
    for (unsigned Offset = 0; Offset < Rdx->Elts.size(); Offset += RdxLen)
      OPs.emplace_back().assign(Rdx->Elts.begin() + Offset,
                                Rdx->Elts.begin() + Offset + RdxLen);
    canonicalizeOperandPacks(OPs);
  } break;
  case GEP: {
    unsigned NumOperands = GEPs.front()->getNumOperands();
    SmallVector<OperandPack, 4> OPs;
    for (unsigned i = 0; i < NumOperands; i++) {
      SmallVector<Value *, 8> Operands;
      getGEPOperands(i, GEPs, Operands);
      if (!is_splat(Operands))
        OPs.emplace_back().assign(Operands);
    }
    canonicalizeOperandPacks(OPs);
  } break;
  case Gamma: {
    unsigned NumIncomings = Gammas.front()->PN->getNumIncomingValues();
    assert(all_of(Gammas, [&](auto *G2) {
      return G2->PN->getNumIncomingValues() == NumIncomings;
    }));

    for (unsigned i = 0; i < NumIncomings; i++) {
      SmallVector<const ControlCondition *> Conds;
      OperandPack ValOP;
      for (auto *G : Gammas) {
        Conds.push_back(G->Conds[i]);
        ValOP.push_back(G->Vals[i]);
      }
      getOperandPacksFromCondition(VPCtx->getConditionPack(Conds),
                                   OperandPacks);
      OperandPacks.push_back(VPCtx->getCanonicalOperandPack(ValOP));
    }
  } break;
  case Cmp: {
    SmallVector<OperandPack, 2> OPs;
    OPs.resize(2);
    for (unsigned i : {0, 1}) {
      for (auto *Cmp : Cmps)
        OPs[i].push_back(Cmp->getOperand(i));
    }
    canonicalizeOperandPacks(OPs);
  } break;

  } // end switch

  if (CP)
    getOperandPacksFromCondition(CP, OperandPacks);
}

static Value *emitVectorGEP(ArrayRef<GetElementPtrInst *> GEPs,
                            ArrayRef<Value *> Operands,
                            IRBuilderBase &Builder) {
  SmallVector<Value *, 4> Ptrs;
  getGEPOperands(0, GEPs, Ptrs);

  Value *Ptr;
  bool BroadcastPtr = is_splat(Ptrs);
  unsigned j = 0;
  if (BroadcastPtr)
    Ptr = Ptrs.front();
  else
    Ptr = Operands[j++];

  unsigned NumOperands = GEPs.front()->getNumOperands();
  SmallVector<Value *, 4> Idxs;
  for (unsigned i = 1; i < NumOperands; i++) {
    SmallVector<Value *, 4> Values;
    getGEPOperands(i, GEPs, Values);
    if (is_splat(Values))
      Idxs.push_back(Values.front());
    else
      Idxs.push_back(Operands[j++]);
  }
  return Builder.CreateGEP(GEPs.front()->getSourceElementType(), Ptr, Idxs);
}

static Value *emitVectorCmp(ArrayRef<CmpInst *> Cmps,
                            ArrayRef<Value *> Operands,
                            IntrinsicBuilder &Builder) {
  auto Pred = Cmps.front()->getPredicate();
  assert(Operands.size() == 2);
  return Builder.CreateCmp(Pred, Operands[0], Operands[1]);
}

Value *VectorPack::emit(ArrayRef<Value *> Operands,
                        IntrinsicBuilder &Builder) const {
  IRBuilderBase::InsertPointGuard Guard(Builder);

  // FIXME: choose insert point
  switch (Kind) {
  case General:
    return emitVectorGeneral(Operands, Builder);
  case GEP:
    return emitVectorGEP(GEPs, Operands, Builder);
  case Cmp:
    return emitVectorCmp(Cmps, Operands, Builder);
  case Load:
  case Store:
  case Reduction:
  case Gamma:
  case Phi:
    llvm_unreachable("Don't call emit on reduction and gamma pack directly");
  }
}

void VectorPack::computeCost(TargetTransformInfo *TTI) {
  Cost = 0;
  // 1) First figure out cost of the vector instruction
  switch (Kind) {
  case General:
    Cost = Producer->getCost(TTI, VPCtx->getFunction()->getContext());
    break;
  case Load: {
    auto *LI = Loads[0];
    auto *VecTy = FixedVectorType::get(LI->getType(), Loads.size());
    if (IsGatherScatter) {
      Cost = TTI->getGatherScatterOpCost(
          Instruction::Load, VecTy, LI->getPointerOperand(),
          false /*variable mask*/, getCommonAlignment(Loads),
          TTI::TCK_RecipThroughput, LI);
    } else {
      Cost = TTI->getMemoryOpCost(Instruction::Load, VecTy, LI->getAlign(), 0,
                                  TTI::TCK_RecipThroughput, LI);
    }
    break;
  }
  case Store: {
    auto *SI = Stores[0];
    auto *VecTy =
        FixedVectorType::get(SI->getValueOperand()->getType(), Stores.size());
    if (IsGatherScatter) {
      Cost = TTI->getGatherScatterOpCost(
          Instruction::Store, VecTy, SI->getPointerOperand(),
          false /*variable mask*/, getCommonAlignment(Stores),
          TTI::TCK_RecipThroughput, SI);
    } else {
      Cost = TTI->getMemoryOpCost(Instruction::Store, VecTy, SI->getAlign(), 0,
                                  TTI::TCK_RecipThroughput, SI);
    }
    break;
  }
  case Cmp:
    // FIXME: call TTI
    Cost = 1;
    break;
  case Phi:
    Cost = 0;
    break;
  case Reduction:
    // FIXME: actually compute the cost
    Cost = 4;
    break;
  case GEP:
    Cost = 0;
    break;
  case Gamma:
    // FIXME call TTI
    Cost = 1;
    break;
  }

  ProducingCost = Cost;
}

void VectorPack::computeOrderedValues() {
  switch (Kind) {
  case General:
    transform(Matches, std::back_inserter(OrderedValues),
              [](auto *M) { return M ? M->Output : nullptr; });
    break;
  case Load:
    OrderedValues.assign(Loads.begin(), Loads.end());
    break;
  case Store:
    OrderedValues.assign(Stores.begin(), Stores.end());
    break;
  case Phi:
    OrderedValues.assign(PHIs.begin(), PHIs.end());
    break;
  case Reduction:
    OrderedValues.push_back(Rdx->Ops.front());
    break;
  case GEP:
    OrderedValues.assign(GEPs.begin(), GEPs.end());
    break;
  case Cmp:
    OrderedValues.assign(Cmps.begin(), Cmps.end());
    break;
  case Gamma:
    for (auto *G : Gammas)
      OrderedValues.push_back(G->PN);
    break;
  }
}

// Choose a right place to gather an operand
void VectorPack::setOperandGatherPoint(unsigned OperandId,
                                       IntrinsicBuilder &Builder) const {
  if (Kind != Phi) {
    auto *LeaderVal = *getOrderedValues().begin();
    Builder.SetInsertPoint(cast<Instruction>(LeaderVal));
  } else {
    // We need to gather the input before the execution gets to this block
    auto *FirstPHI = PHIs[0];
    auto *BB = FirstPHI->getIncomingBlock(OperandId);
    Builder.SetInsertPoint(BB->getTerminator());
  }
}

raw_ostream &operator<<(raw_ostream &OS, const VectorPack &VP) {
  StringRef ProducerName = "";
  if (auto *Producer = VP.getProducer())
    ProducerName = Producer->getName();
  else if (VP.isGamma())
    ProducerName = "Gamma";
  else if (VP.isReduction())
    ProducerName = "reduction";
  else if (VP.IsGatherScatter)
    ProducerName = "gather/scatter";

  OS << "PACK<" << ProducerName << ">: (\n";
  for (auto *V : VP.getOrderedValues())
    if (V)
      OS << *V << '\n';
    else
      OS << "undef\n";
  OS << ")\n";
  return OS;
}

raw_ostream &operator<<(raw_ostream &OS, const OperandPack &OP) {
  OS << "[\n";
  for (auto *V : OP)
    if (V) {
      errs() << *V << "\n";
    } else
      errs() << "undef\n";
  OS << "\n]";
  return OS;
}

FixedVectorType *getVectorType(const OperandPack &OP) {
  if (OP.Ty)
    return OP.Ty;
  Type *ScalarTy = nullptr;
  for (auto *V : OP)
    if (V) {
      ScalarTy = V->getType();
      break;
    }
  assert(ScalarTy && "Operand pack can't be all empty");
  return OP.Ty = FixedVectorType::get(ScalarTy, OP.size());
}

FixedVectorType *getVectorType(const VectorPack &VP) {
  unsigned NumLanes = VP.getElements().count();
  auto *FirstLane = *VP.elementValues().begin();
  return FixedVectorType::get(FirstLane->getType(), NumLanes);
}

bool isConstantPack(const OperandPack &OP) {
  for (auto *V : OP)
    if (V && !isa<Constant>(V))
      return false;
  return true;
}

void VectorPack::getPackedInstructions(
    SmallPtrSetImpl<Instruction *> &Insts) const {
  if (Kind != General) {
    for (auto *V : elementValues())
      Insts.insert(cast<Instruction>(V));
    return;
  }

  SmallPtrSet<Value *, 32> LiveIns;
  SmallVector<Value *> Worklist;
  for (auto *M : Matches) {
    if (!M)
      continue;
    LiveIns.insert(M->Inputs.begin(), M->Inputs.end());
    Worklist.push_back(M->Output);
  }
  while (!Worklist.empty()) {
    auto *I = dyn_cast<Instruction>(Worklist.pop_back_val());
    if (!I || LiveIns.count(I))
      continue;
    if (!Insts.insert(I).second)
      continue;
    Worklist.append(I->value_op_begin(), I->value_op_end());
  }
}

Value *VectorPack::getLoadStorePointer() const {
  if (IsGatherScatter)
    return nullptr;
  if (isLoad())
    return Loads.front()->getPointerOperand();
  else if (isStore())
    return Stores.front()->getPointerOperand();
  return nullptr;
}
