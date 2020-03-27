#include "VectorPack.h"

using namespace llvm;

// FIXME: we need to generalize the definition of an operand pack
// because some of the input lanes are "DONT CARES" (e.g. _mm_div_pd)
std::vector<VectorPack::OperandPack>
VectorPack::getOperandPacksForGeneral() const {
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
    // Find output lanes that uses input `i` and record those uses
    for (unsigned j = 0; j < NumLanes; j++) {
      ArrayRef<InputSlice> BoundSlices = LaneOps[j].getBoundSlices();
      for (unsigned k = 0; k < BoundSlices.size(); k++) {
        auto &BS = BoundSlices[k];
        if (BS.InputId != i)
          continue;
        InputValues.push_back({BS, Matches[j] ? Matches[j]->Inputs[k] : nullptr});
      }
    }

    // Sort the input values by their slice offset
    std::sort(InputValues.begin(), InputValues.end());

    unsigned CurOffset = 0;
    unsigned Stride = InputValues[0].Slice.size();
    auto &OpndPack = OperandPacks[i];
    for (const BoundInput &BV : InputValues) {
      while (CurOffset < BV.Slice.Lo) {
        OpndPack.push_back(nullptr);
        CurOffset += Stride;
      }
      assert(CurOffset == BV.Slice.Lo);
      OpndPack.push_back(BV.V);
      CurOffset += Stride;
    }
    unsigned InputSize = Sig.InputBitwidths[i];
    while (CurOffset < InputSize) {
      OpndPack.push_back(nullptr);
      CurOffset += Stride;
    }
    assert(OpndPack.size() * Stride == InputSize);
  }
  return OperandPacks;
}

std::vector<VectorPack::OperandPack>
VectorPack::getOperandPacksForLoad() const {
  // Only need the single *scalar* pointer, doesn't need packed operand
  return std::vector<OperandPack>();
}

std::vector<VectorPack::OperandPack>
VectorPack::getOperandPacksForStore() const {
  std::vector<OperandPack> UPs(1);
  auto &OpndPack = UPs[0];
  // Don't care about the pointers,
  // only the values being stored need to be packed first
  for (auto *S : Stores)
    OpndPack.push_back(S->getValueOperand());
  return UPs;
}

std::vector<VectorPack::OperandPack> VectorPack::getOperandPacksForPhi() const {
  auto *FirstPHI = PHIs[0];
  unsigned NumIncomings = FirstPHI->getNumIncomingValues();
  // We need as many packs as there are incoming edges
  std::vector<OperandPack> UPs(NumIncomings);
  for (unsigned i = 0; i < NumIncomings; i++) {
    auto *BB = FirstPHI->getIncomingBlock(i);
    // all of the values coming from BB should be packed
    for (auto *PH : PHIs)
      UPs[i].push_back(PH->getIncomingValueForBlock(BB));
  }
  return UPs;
}

static Type *getScalarTy(ArrayRef<Optional<Operation::Match>> Matches) {
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
  auto *VecType = VectorType::get(getScalarTy(Matches), Matches.size());
  return Builder.CreateBitCast(VecInst, VecType);
}

// Shameless stolen from llvm's SLPVectorizer
Value *VectorPack::emitVectorLoad(ArrayRef<Value *> Operands,
                                  IntrinsicBuilder &Builder) const {
  auto *FirstLoad = Loads[0];
  auto &DL = FirstLoad->getParent()->getModule()->getDataLayout();
  auto *ScalarLoadTy = FirstLoad->getType();

  // Figure out type of the vector that we are loading
  auto *ScalarPtr = FirstLoad->getPointerOperand();
  auto *ScalarTy = cast<PointerType>(ScalarPtr->getType())->getElementType();
  auto *VecTy = VectorType::get(ScalarTy, Loads.size());

  // Cast the scalar pointer to a vector pointer
  unsigned AS = FirstLoad->getPointerAddressSpace();
  Value *VecPtr = Builder.CreateBitCast(ScalarPtr, VecTy->getPointerTo(AS));

  // Emit the load
  auto *VecLoad = Builder.CreateLoad(VecTy, VecPtr);

  // Set alignment data
  MaybeAlign Alignment = MaybeAlign(FirstLoad->getAlignment());
  if (!Alignment)
    Alignment = MaybeAlign(DL.getABITypeAlignment(ScalarLoadTy));
  VecLoad->setAlignment(Alignment);

  std::vector<Value *> Values(Loads.begin(), Loads.end());
  return propagateMetadata(VecLoad, Values);
}

Value *VectorPack::emitVectorStore(ArrayRef<Value *> Operands,
                                   IntrinsicBuilder &Builder) const {
  auto *FirstStore = Stores[0];

  // This is the value we want to store
  Value *VecValue = Operands[0];

  // Figure out the store alignment
  unsigned Alignment = FirstStore->getAlignment();
  unsigned AS = FirstStore->getPointerAddressSpace();

  // Cast the scalar pointer to vector pointer
  assert(Operands.size() == 1);
  Value *ScalarPtr = FirstStore->getPointerOperand();
  Value *VecPtr =
      Builder.CreateBitCast(ScalarPtr, VecValue->getType()->getPointerTo(AS));

  // Emit the vector store
  StoreInst *VecStore = Builder.CreateStore(VecValue, VecPtr);

  // Fix the vector store alignment
  auto &DL = FirstStore->getParent()->getModule()->getDataLayout();
  if (!Alignment)
    Alignment =
        DL.getABITypeAlignment(FirstStore->getValueOperand()->getType());

  VecStore->setAlignment(Align(Alignment));
  std::vector<Value *> Stores_(Stores.begin(), Stores.end());
  return propagateMetadata(VecStore, Stores_);
}

Value *VectorPack::emitVectorPhi(ArrayRef<Value *> Operands,
                                 IntrinsicBuilder &Builder) const {
  auto *BB = VPCtx->getBasicBlock();
  Builder.SetInsertPoint(&*BB->begin());
  auto *FirstPHI = PHIs[0];
  unsigned NumIncomings = FirstPHI->getNumIncomingValues();

  auto *VecTy = VectorType::get(FirstPHI->getType(), PHIs.size());
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

const std::vector<VectorPack::OperandPack> VectorPack::getOperandPacks() const {
  switch (Kind) {
  case General:
    return getOperandPacksForGeneral();
  case Load:
    return getOperandPacksForLoad();
  case Store:
    return getOperandPacksForStore();
  case Phi:
    return getOperandPacksForPhi();
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
  }
}

int VectorPack::getCost(TargetTransformInfo *TTI, LLVMContext &Ctx) const {
  switch (Kind) {
  case General:
    return Producer->getCost(TTI, Ctx);
  case Load: {
    auto *LI = Loads[0];
    MaybeAlign Alignment(LI->getAlignment());
    auto *VecTy = VectorType::get(LI->getType(), Loads.size());
    return TTI->getMemoryOpCost(Instruction::Load, VecTy, Alignment, 0, LI);
  }
  case Store: {
    auto *SI = Stores[0];
    MaybeAlign Alignment(SI->getAlignment());
    auto *VecTy =
        VectorType::get(SI->getValueOperand()->getType(), Stores.size());
    return TTI->getMemoryOpCost(Instruction::Store, VecTy, Alignment, 0, SI);
  }
  case Phi:
    return 0;
  }
}

std::vector<Value *> VectorPack::getOrderedValues() const {
  std::vector<Value *> OrderedValues;
  switch (Kind) {
  case General:
    for (auto &M : Matches)
      if (M)
        OrderedValues.push_back(M->Output);
      else
        OrderedValues.push_back(nullptr);
    break;
  case Load:
    for (auto *LI : Loads)
      OrderedValues.push_back(LI);
    break;
  case Store:
    for (auto *SI : Stores)
      OrderedValues.push_back(SI);
    break;
  case Phi:
    for (auto *PHI : PHIs)
      OrderedValues.push_back(PHI);
    break;
  }
  return OrderedValues;
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
  OS << "PACK<" << ProducerName << ">: (\n";
  for (auto *V : VP.getOrderedValues())
    OS << *V << '\n';
  OS << ")\n";
  return OS;
}
