#include "VectorPack.h"
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

Value *VectorPack::emitVectorLoad(ArrayRef<Value *> Operands,
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
    VecLoad =
        Builder.CreateMaskedGather(Operands.front(), getCommonAlignment(Loads));
  else
    VecLoad = Builder.CreateAlignedLoad(VecTy, VecPtr, FirstLoad->getAlign());

  std::vector<Value *> Values;
  for (auto *LI : Loads)
    if (LI)
      Values.push_back(LI);
  return propagateMetadata(VecLoad, Values);
}

Value *VectorPack::emitVectorStore(ArrayRef<Value *> Operands,
                                   IntrinsicBuilder &Builder) const {

  // This is the value we want to store

  // Emit the vector store
  Instruction *VecStore;
  if (IsGatherScatter) {
    auto *Ptrs = Operands[0];
    auto *Values = Operands[1];
    VecStore =
        Builder.CreateMaskedScatter(Values, Ptrs, getCommonAlignment(Stores));
  } else {
    Value *VecValue = Operands.front();
    auto *FirstStore = Stores.front();

    // Figure out the store alignment
    unsigned Alignment = FirstStore->getAlignment();
    unsigned AS = FirstStore->getPointerAddressSpace();

    // Cast the scalar pointer to vector pointer
    assert(Operands.size() == 1);
    Value *ScalarPtr = FirstStore->getPointerOperand();
    Value *VecPtr =
        Builder.CreateBitCast(ScalarPtr, VecValue->getType()->getPointerTo(AS));

    VecStore = Builder.CreateStore(VecValue, VecPtr);

    // Fix the vector store alignment
    auto &DL = FirstStore->getParent()->getModule()->getDataLayout();
    if (!Alignment)
      Alignment =
          DL.getABITypeAlignment(FirstStore->getValueOperand()->getType());

    cast<StoreInst>(VecStore)->setAlignment(Align(Alignment));
  }

  SmallVector<Value *, 4> Stores_(Stores.begin(), Stores.end());
  return propagateMetadata(VecStore, Stores_);
}

Value *VectorPack::emitVectorPhi(ArrayRef<Value *> Operands,
                                 IntrinsicBuilder &Builder) const {
  auto *BB = PHIs.front()->getParent();
  Builder.SetInsertPoint(&*BB->begin());
  auto *FirstPHI = PHIs.front();
  unsigned NumIncomings = FirstPHI->getNumIncomingValues();

  auto *VecTy = FixedVectorType::get(FirstPHI->getType(), PHIs.size());
  auto *VecPHI = Builder.CreatePHI(VecTy, NumIncomings);

  std::set<BasicBlock *> Visited;
  // Values in operands follow the order of ::getUserPack,
  // which follows the basic block order of the first phi.
  for (unsigned i = 0; i < NumIncomings; i++) {
    auto *BB = FirstPHI->getIncomingBlock(i);
    // Apparently sometimes a phi node can have more than one
    // incoming value for the same basic block...
    if (Visited.count(BB)) {
      VecPHI->addIncoming(VecPHI->getIncomingValueForBlock(BB), BB);
      continue;
    }
    auto *VecIncoming = Operands[i];
    VecPHI->addIncoming(VecIncoming, BB);
    Visited.insert(BB);
  }
  assert(VecPHI->getNumIncomingValues() == FirstPHI->getNumIncomingValues());
  return VecPHI;
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
  case Reduction:
    OperandPack OP;
    OP.assign(Rdx->Elts.begin(), Rdx->Elts.end());
    canonicalizeOperandPacks({OP});
  }
}

Value *VectorPack::emit(ArrayRef<Value *> Operands,
                        IntrinsicBuilder &Builder) const {
  IRBuilderBase::InsertPointGuard Guard(Builder);

  // FIXME: choose insert point
  switch (Kind) {
  case General:
    return emitVectorGeneral(Operands, Builder);
  case Load:
    return emitVectorLoad(Operands, Builder);
  case Store:
    return emitVectorStore(Operands, Builder);
  case Phi:
    return emitVectorPhi(Operands, Builder);
  case Reduction:
    llvm_unreachable("Don't call emit on reduction pack directly");
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
  case Phi:
    Cost = 0;
    break;
  case Reduction:
    // FIXME: actually compute the cost
    Cost = 4;
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
    OrderedValues.append(Loads.begin(), Loads.end());
    break;
  case Store:
    OrderedValues.append(Stores.begin(), Stores.end());
    break;
  case Phi:
    OrderedValues.append(PHIs.begin(), PHIs.end());
    break;
  case Reduction:
    OrderedValues.push_back(Rdx->Ops.front());
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
  else if (VP.isReduction())
    ProducerName = "reduction";
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
