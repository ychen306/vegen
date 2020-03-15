#include "InstSema.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/MemoryLocation.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/Analysis/VectorUtils.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/InitializePasses.h"
#include "llvm/Linker/Linker.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/InstCombine/InstCombine.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/InstSimplifyPass.h"
#include <set>

using namespace llvm;
using namespace PatternMatch;

cl::opt<std::string> InstWrappersPath("inst-wrappers",
                                      cl::desc("Path to InstWrappers.bc"),
                                      cl::Required);

namespace llvm {
void initializeGSLPPass(PassRegistry &);
}

namespace {

bool isFloat(Instruction::BinaryOps Opcode) {
  switch (Opcode) {
  case Instruction::FAdd:
  case Instruction::FSub:
  case Instruction::FMul:
  case Instruction::FDiv:
  case Instruction::FRem:
    return true;
  default:
    return false;
  }
}

// TODO: Support LOAD, STORE, and PHI
class BinaryIROperation : public Operation {
  const Instruction::BinaryOps Opcode;
  unsigned Bitwidth;

public:
  BinaryIROperation(Instruction::BinaryOps Opcode, unsigned Bitwidth)
      : Opcode(Opcode), Bitwidth(Bitwidth) {}
  std::string getName() const { return Instruction::getOpcodeName(Opcode); }
  unsigned getBitwidth() const { return Bitwidth; }
  const Instruction::BinaryOps getOpcode() const { return Opcode; }
  bool match(llvm::Value *V, std::vector<Match> &Matches) const override {
    auto *BinOp = dyn_cast<BinaryOperator>(V);
    bool Matched =
        BinOp && BinOp->getOpcode() == Opcode && hasBitWidth(BinOp, Bitwidth);
    if (Matched)
      Matches.push_back({// live ins of this operation
                         {BinOp->getOperand(0), BinOp->getOperand(1)},
                         V});
    return Matched;
  }
};

class IRVectorBinding : public InstBinding {
  const BinaryIROperation *Op;

  IRVectorBinding(const BinaryIROperation *Op, std::string Name,
                  InstSignature Sig, std::vector<BoundOperation> LaneOps)
      : InstBinding(Name, Sig, LaneOps), Op(Op) {}

public:
  static IRVectorBinding Create(const BinaryIROperation *Op,
                                unsigned VectorWidth);
  virtual Value *emit(ArrayRef<llvm::Value *> Operands,
                      IntrinsicBuilder &Builder) const override;
  int getCost(TargetTransformInfo *TTI, LLVMContext &Ctx) const override {
    Type *ScalarTy;
    unsigned ElemWidth = Op->getBitwidth();
    auto Opcode = Op->getOpcode();
    if (isFloat(Opcode)) {
      assert(ElemWidth == 32 || ElemWidth == 64);
      if (ElemWidth == 32)
        ScalarTy = Type::getFloatTy(Ctx);
      else
        ScalarTy = Type::getDoubleTy(Ctx);
    } else {
      ScalarTy = IntegerType::get(Ctx, ElemWidth);
    }
    unsigned NumElems = getLaneOps().size();
    auto *VecTy = VectorType::get(ScalarTy, NumElems);
    return TTI->getVectorInstrCost(Opcode, VecTy);
  }
};

class GSLP : public FunctionPass {
  std::unique_ptr<Module> InstWrappers;

public:
  static char ID; // Pass identification, replacement for typeid
  GSLP() : FunctionPass(ID) {
    initializeGSLPPass(*PassRegistry::getPassRegistry());
  }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<ScalarEvolutionWrapperPass>();
    AU.addRequired<AAResultsWrapperPass>();
    AU.addRequired<TargetTransformInfoWrapperPass>();
  }

  bool runOnFunction(Function &) override;

  virtual bool doInitialization(Module &M) override {
    SMDiagnostic Err;
    errs() << "LOADING WRAPPERS\n";
    InstWrappers = parseIRFile(InstWrappersPath, Err, M.getContext());
    assert(InstWrappers && "Failed to parse Inst Wrappers");
    errs() << "WRAPPERS LOADED\n";

    return false;
  }
};

MemoryLocation getLocation(Instruction *I, AliasAnalysis *AA) {
  if (StoreInst *SI = dyn_cast<StoreInst>(I))
    return MemoryLocation::get(SI);
  if (LoadInst *LI = dyn_cast<LoadInst>(I))
    return MemoryLocation::get(LI);
  return MemoryLocation();
}

/// \returns True if the instruction is not a volatile or atomic load/store.
bool isSimple(Instruction *I) {
  if (LoadInst *LI = dyn_cast<LoadInst>(I))
    return LI->isSimple();
  if (StoreInst *SI = dyn_cast<StoreInst>(I))
    return SI->isSimple();
  if (MemIntrinsic *MI = dyn_cast<MemIntrinsic>(I))
    return !MI->isVolatile();
  return true;
}

bool isAliased(const MemoryLocation &Loc1, Instruction *Inst1,
               Instruction *Inst2, AliasAnalysis *AA) {
  MemoryLocation Loc2 = getLocation(Inst2, AA);
  bool Aliased = true;
  if (Loc1.Ptr && Loc2.Ptr && isSimple(Inst1) && isSimple(Inst2)) {
    // Do the alias check.
    Aliased = AA->alias(Loc1, Loc2);
  }
  return Aliased;
}

std::vector<Instruction::BinaryOps> VectorizableOpcodes = {
    Instruction::BinaryOps::Add,  Instruction::BinaryOps::FAdd,
    Instruction::BinaryOps::Sub,  Instruction::BinaryOps::FSub,
    Instruction::BinaryOps::Mul,  Instruction::BinaryOps::FMul,
    Instruction::BinaryOps::UDiv, Instruction::BinaryOps::SDiv,
    Instruction::BinaryOps::FDiv, Instruction::BinaryOps::URem,
    Instruction::BinaryOps::SRem, Instruction::BinaryOps::FRem,
    Instruction::BinaryOps::Shl,  Instruction::BinaryOps::LShr,
    Instruction::BinaryOps::AShr, Instruction::BinaryOps::And,
    Instruction::BinaryOps::Or,   Instruction::BinaryOps::Xor};

// Aux class enumerating vector ir that we can emit
class VectorizableTable {
  std::vector<BinaryIROperation> VectorizableOps;
  std::vector<IRVectorBinding> VectorInsts;

  std::vector<InstBinding *> Bindings;

public:
  VectorizableTable() {
    // enumerate vectorizable scalar ops
    std::vector<unsigned> ScalarBitwidths = {8, 16, 32, 64};
    for (auto Opcode : VectorizableOpcodes)
      for (unsigned SB : ScalarBitwidths) {
        if (isFloat(Opcode) && SB != 32 && SB != 64)
          continue;
        VectorizableOps.emplace_back(Opcode, SB);
      }

    // enumerate vector insts
    std::vector<unsigned> VectorBitwidths = {64, 128, 256};
    for (auto &Op : VectorizableOps)
      for (unsigned VB : VectorBitwidths)
        VectorInsts.emplace_back(IRVectorBinding::Create(&Op, VB));

    for (auto &Binding : VectorInsts)
      Bindings.push_back(&Binding);
  }

  ArrayRef<InstBinding *> getBindings() const { return Bindings; }

} VecBindingTable;

// This class pulls all operation that we are interested in
// and tries to match all of them while trying to avoid
// matching the same operation twice on the same value
class MatchManager {
  // record matches for each operation
  DenseMap<const Operation *, std::vector<Operation::Match>> Matches;

public:
  MatchManager() = default;
  MatchManager(ArrayRef<InstBinding *> Insts) {
    for (auto &Inst : Insts)
      for (auto &LaneOp : Inst->getLaneOps())
        Matches.FindAndConstruct(LaneOp.getOperation());
  }

  void match(Value *V) {
    for (auto &KV : Matches) {
      const Operation *Op = KV.first;
      std::vector<Operation::Match> &Matches = KV.second;
      Op->match(V, Matches);
    }
  }

  llvm::ArrayRef<Operation::Match> getMatches(const Operation *Op) const {
    auto It = Matches.find(Op);
    assert(It != Matches.end());
    return It->second;
  }
};

// VectorPackContext captures various meta data we use to create and manage
// vector packs. Basically we want to store vector packs are a bitvector, and we
// need this class to manage the mapping between a value and its integer id
class VectorPack;
class VectorPackContext {
  BasicBlock *BB;
  std::vector<Value *> Scalars;

  using MatchedOperation = std::pair<const Operation *, const Value *>;
  DenseMap<MatchedOperation, Operation::Match> MatchedOps;

public:
  VectorPackContext(BasicBlock *BB) : BB(BB) {
    for (auto &I : *BB)
      Scalars.push_back(&I);
    std::sort(Scalars.begin(), Scalars.end());
  }

  void trackMatchedOperation(const Operation::Match &Match,
                             const Operation *Op) {
    MatchedOps[{Op, Match.Output}] = Match;
  }

  // Create a "General" vector pack
  VectorPack createVectorPack(std::vector<Operation::Match> Matches,
                              BitVector Elements, BitVector Depended,
                              const InstBinding *Producer);

  // Create a vectorized load
  VectorPack createLoadPack(ArrayRef<LoadInst *> Loads, BitVector Elements,
                            BitVector Depended);

  // Create a vectorized store
  VectorPack createStorePack(ArrayRef<StoreInst *> Stores, BitVector Elements,
                             BitVector Depended);

  // Create a vectorized phi
  VectorPack createPhiPack(ArrayRef<PHINode *> PHIs);

  Value *getScalar(unsigned Id) const {
    assert(Id < Scalars.size());
    return Scalars[Id];
  }

  unsigned getScalarId(const Value *V) const {
    auto It = std::lower_bound(Scalars.begin(), Scalars.end(), V);
    assert(It != Scalars.end());
    return It - Scalars.begin();
  }

  unsigned getNumValues() const { return Scalars.size(); }
  BasicBlock *getBasicBlock() const { return BB; }

  // Fixme : templatize this to decouple use of bitvector
  class value_iterator {
    const VectorPackContext *VPCtx;
    BitVector::const_set_bits_iterator Handle;

  public:
    value_iterator(const VectorPackContext *VPCtx,
                   BitVector::const_set_bits_iterator Handle)
        : VPCtx(VPCtx), Handle(Handle) {}
    Value *operator*() {
      unsigned Id = *Handle;
      return VPCtx->getScalar(Id);
    }

    value_iterator &operator++() {
      ++Handle;
      return *this;
    }

    bool operator!=(const value_iterator &It) { return Handle != It.Handle; }
  };

  iterator_range<value_iterator> iter_values(BitVector Ids) const {
    value_iterator Begin(this, Ids.set_bits_begin()),
        End(this, Ids.set_bits_end());
    return make_range(Begin, End);
  }
};

// Utility class to track dependency within a basic block
class LocalDependenceAnalysis {
  BasicBlock *BB;
  // mapping inst -> <users>
  DenseMap<Instruction *, std::vector<Instruction *>> Dependencies;
  VectorPackContext &VPCtx;
  // mapping an instruction -> instructions that it transitively depends on
  DenseMap<Instruction *, BitVector> TransitiveClosure;

public:
  LocalDependenceAnalysis(AliasAnalysis *AA, BasicBlock *BB,
                          VectorPackContext &VPCtx)
      : BB(BB), VPCtx(VPCtx) {
    std::vector<Instruction *> LoadStores;
    // build the local dependence graph
    for (Instruction &I : *BB) {
      // PHINodes do not introduce any local dependence
      if (isa<PHINode>(&I))
        continue;

      for (Value *Operand : I.operands()) {
        if (auto *I2 = dyn_cast<Instruction>(Operand))
          if (I2->getParent() == BB) {
            Dependencies[&I].push_back(I2);
          }
      }
      if (isa<LoadInst>(&I) || isa<StoreInst>(&I)) {
        MemoryLocation Loc = getLocation(&I, AA);
        // check dependence with preceding loads and stores
        for (auto *PrevLS : LoadStores) {
          // ignore output dependence
          if (isa<LoadInst>(PrevLS) && isa<LoadInst>(&I))
            continue;
          if (isAliased(Loc, &I, PrevLS, AA))
            Dependencies[&I].push_back(PrevLS);
        }
        LoadStores.push_back(&I);
      }
    }
  }

  BitVector getDepended(Instruction *I) {
    auto It = TransitiveClosure.try_emplace(I, BitVector(VPCtx.getNumValues()));
    BitVector &Depended = It.first->second;
    bool Inserted = It.second;
    if (!Inserted)
      return Depended;

    for (auto *Src : Dependencies[I])
      Depended |= getDepended(Src);

    return Depended;
  }
};

// A vector pack is an *ordered* set of values,
// these values should come from the same basic block
class VectorPack {

public:
  // Use this to model input operands
  using OperandPack = SmallVector<Value *, 8>;

  enum PackKind { General, Phi, Load, Store };

private:
  friend class VectorPackContext;

  const VectorPackContext *VPCtx;
  BitVector Elements;
  BitVector Depended;

  //////////// Data for the 4 kinds
  PackKind Kind;
  // General
  struct {
    // SmallVector<Operation::Match, 4> Matches;
    std::vector<Operation::Match> Matches;
    const InstBinding *Producer;
  };
  // Load
  std::vector<LoadInst *> Loads;
  // Store
  std::vector<StoreInst *> Stores;
  // PHI
  std::vector<PHINode *> PHIs;
  ///////////////

  // Constructor for a generic pack
  VectorPack(const VectorPackContext *VPCtx, ArrayRef<Operation::Match> Matches,
             BitVector Elements, BitVector Depended,
             const InstBinding *Producer)
      : VPCtx(VPCtx), Elements(Elements), Depended(Depended),
        Kind(PackKind::General), Producer(Producer), Matches(Matches) {}

  // Load Pack
  VectorPack(const VectorPackContext *VPCtx, ArrayRef<LoadInst *> Loads,
             BitVector Elements, BitVector Depended)
      : VPCtx(VPCtx), Elements(Elements), Depended(Depended),
        Kind(PackKind::Load), Loads(Loads) {}

  // Store Pack
  VectorPack(const VectorPackContext *VPCtx, ArrayRef<StoreInst *> Stores,
             BitVector Elements, BitVector Depended)
      : VPCtx(VPCtx), Elements(Elements), Depended(Depended),
        Kind(PackKind::Store), Stores(Stores) {}

  // Load Pack
  VectorPack(const VectorPackContext *VPCtx, ArrayRef<PHINode *> PHIs,
             BitVector Elements, BitVector Depended)
      : VPCtx(VPCtx), Elements(Elements), Depended(Depended),
        Kind(PackKind::Phi), PHIs(PHIs) {}

  std::vector<OperandPack> getOperandPacksForGeneral() const {
    auto &Sig = Producer->getSignature();
    unsigned NumInputs = Sig.numInputs();
    auto LaneOps = Producer->getLaneOps();
    unsigned NumLanes = LaneOps.size();
    std::vector<OperandPack> OperandPacks(NumInputs);

    struct BoundInput {
      InputSlice S;
      Value *V;
      // Order by offset of the slice
      bool operator<(const BoundInput &Other) const { return S < Other.S; }
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
          InputValues.push_back({BS, Matches[j].Inputs[k]});
        }
      }

      // Sort the input values by their slice offset
      std::sort(InputValues.begin(), InputValues.end());
      for (const BoundInput &BV : InputValues)
        OperandPacks[i].push_back(BV.V);
    }
    return OperandPacks;
  }

  std::vector<OperandPack> getOperandPacksForLoad() const {
    // Only need the single *scalar* pointer, doesn't need packed operand
    return std::vector<OperandPack>();
  }

  std::vector<OperandPack> getOperandPacksForStore() const {
    std::vector<OperandPack> UPs(1);
    auto &OpndPack = UPs[0];
    // Don't care about the pointers,
    // only the values being stored need to be packed first
    for (auto *S : Stores)
      OpndPack.push_back(S->getValueOperand());
    return UPs;
  }

  std::vector<OperandPack> getOperandPacksForPhi() const {
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

  // Shameless stolen from llvm's SLPVectorizer
  Value *emitVectorLoad(ArrayRef<Value *> Operands,
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

  Value *emitVectorStore(ArrayRef<Value *> Operands,
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

  Value *emitVectorPhi(ArrayRef<Value *> Operands,
                       IntrinsicBuilder &Builder) const {
    auto *FirstPHI = PHIs[0];
    unsigned NumIncomings = FirstPHI->getNumIncomingValues();

    auto *VecTy = VectorType::get(FirstPHI->getType(), PHIs.size());
    auto *VecPHI = Builder.CreatePHI(VecTy, NumIncomings);

    // Values in operands follow the order of ::getUserPack,
    // which follows the basic block order of the first phi.
    for (unsigned i = 0; i < NumIncomings; i++) {
      auto *BB = FirstPHI->getIncomingBlock(i);
      auto *VecIncoming = Operands[i];
      VecPHI->addIncoming(VecIncoming, BB);
    }
    assert(VecPHI->getNumIncomingValues() == FirstPHI->getNumIncomingValues());
    return VecPHI;
  }

public:
  VectorPack(const VectorPack &Other) = default;
  VectorPack &operator=(const VectorPack &Other) = default;

  const VectorPackContext *getContext() const { return VPCtx; }

  iterator_range<VectorPackContext::value_iterator> elementValues() const {
    return VPCtx->iter_values(Elements);
  }

  iterator_range<VectorPackContext::value_iterator> dependedValues() const {
    return VPCtx->iter_values(Depended);
  }

  unsigned numElements() const { return Elements.count(); }

  const BitVector &getDepended() const { return Depended; }

  const BitVector &getElements() const { return Elements; }

  const InstBinding *getProducer() const { return Producer; }

  const std::vector<OperandPack> getOperandPacks() const {
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

  Value *emit(ArrayRef<Value *> Operands, IntrinsicBuilder &Builder) const {
    IRBuilderBase::InsertPointGuard Guard(Builder);

    // FIXME: choose insert point
    switch (Kind) {
    case General:
      return Producer->emit(Operands, Builder);
    case Load:
      return emitVectorLoad(Operands, Builder);
    case Store:
      return emitVectorStore(Operands, Builder);
    case Phi:
      return emitVectorPhi(Operands, Builder);
    }
  }

  // Choose a right place to gather an operand
  void setOperandGatherPoint(unsigned OperandId,
                             IntrinsicBuilder &Builder) const {
    if (Kind != Phi) {
      auto *LeaderVal = *elementValues().begin();
      Builder.SetInsertPoint(cast<Instruction>(LeaderVal));
    } else {
      // We need to gather the input before the execution gets to this block
      auto *FirstPHI = PHIs[0];
      auto *BB = FirstPHI->getIncomingBlock(OperandId);
      Builder.SetInsertPoint(BB->getTerminator());
    }
  }
};

// Topsort the vector packs.
// Also reschedule the basic block according to the sorted packs.
//
// This reordering makes codegen easier because we can
// just insert the vector instruction immediately after the last
// instruction that you are replacing.
std::vector<const VectorPack *>
sortPacksAndScheduleBB(BasicBlock *BB, ArrayRef<VectorPack> Packs,
                       LocalDependenceAnalysis &LDA) {
  if (Packs.empty())
    return std::vector<const VectorPack *>();

  // Mapping values to where they are packed
  DenseMap<Value *, const VectorPack *> ValueToPackMap;
  for (auto &VP : Packs)
    for (Value *V : VP.elementValues())
      ValueToPackMap[V] = &VP;

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
  const VectorPackContext *VPCtx = Packs[0].getContext();
  using InstOrPack = PointerUnion<const Instruction *, const VectorPack *>;
  DenseSet<void *> Reordered;
  std::vector<const Instruction *> ReorderedInsts;
  std::function<void(InstOrPack)> Schedule = [&](InstOrPack IOP) {
    bool Inserted = Reordered.insert(IOP.getOpaqueValue()).second;
    if (!Inserted)
      return;

    auto *I = IOP.dyn_cast<const Instruction *>();
    auto *VP = IOP.dyn_cast<const VectorPack *>();

    // Don't process a packed instruction independently with the rest of a pack
    if (I && ValueToPackMap.count(I))
      return;

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
      auto It = ValueToPackMap.find(V);
      // If the depended value comes from a pack,
      // that pack needs to be reorder as a whole unit.
      if (It != ValueToPackMap.end())
        Schedule(It->second);
      else if (auto *I = dyn_cast<Instruction>(V)) {
        if (I->getParent() == BB)
          Schedule(I);
      }
    }

    // Now reorder this (pack of) instruction(s)
    if (I)
      ReorderedInsts.push_back(I);
    else {
      assert(VP);
      for (auto *V : VP->elementValues())
        ReorderedInsts.push_back(cast<Instruction>(V));
    }
  };

  // Sort the packs first
  for (auto &VP : Packs)
    SortPack(&VP);
  assert(SortedPacks.size() == Packs.size());

  // Now reschedule the whole basic blocks;
  for (auto &I : *BB)
    Schedule(&I);
  for (auto &VP : Packs)
    Schedule(&VP);
  assert(ReorderedInsts.size() == BB->size());

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

class VectorPackSet {
  Function *F;
  DenseMap<BasicBlock *, std::vector<VectorPack>> Packs;
  DenseMap<BasicBlock *, BitVector> PackedValues;

  // This tells us where a value is located in a pack
  struct VectorPackIndex {
    const VectorPack *VP;
    unsigned Idx;
  };

  // Mapping a value to the pack that produce them.
  using ValueIndexTy = DenseMap<const Value *, VectorPackIndex>;
  // Mapping VectorPack -> their materialized values.
  using PackToValueTy = DenseMap<const VectorPack *, Value *>;

  // Get the vector value representing OpndPack.
  static Value *gatherOperandPack(VectorPack::OperandPack OpndPack,
                                  const ValueIndexTy &ValueIndex,
                                  const PackToValueTy &MaterializedPacks,
                                  IntrinsicBuilder &Builder);

  // Use this to iterate over `Packs` if you don't care about grouping them by
  // basic blocks
  struct iterator {
    VectorPackSet *Parent;
    decltype(Packs)::iterator BBIt;
    decltype(Packs)::mapped_type::iterator VPIt;

    const VectorPack &operator*() const { return *VPIt; }

    iterator &operator++() {
      ++VPIt;
      if (VPIt == BBIt->second.end()) {
        ++BBIt;
        if (BBIt != Parent->Packs.end())
          VPIt = BBIt->second.begin();
      }

      return *this;
    }

    bool operator!=(const iterator &Other) const {
      if (BBIt == Parent->Packs.end() && Other.BBIt == Parent->Packs.end())
        return false;
      return std::tie(BBIt, VPIt) != std::tie(Other.BBIt, Other.VPIt);
    }
  };

public:
  VectorPackSet(Function *F) : F(F) {}

  iterator_range<iterator> iter_packs() {
    iterator Begin, End;
    Begin.Parent = this;
    Begin.BBIt = Packs.begin();
    Begin.VPIt = Packs.begin()->second.begin();

    End.Parent = this;
    End.BBIt = Packs.end();

    return make_range(Begin, End);
  }

  // Add VP to this set if it doesn't conflict with existing packs.
  // return if successful
  bool tryAdd(BasicBlock *BB, VectorPack VP);

  // Estimate cost of this pack
  int getCostSaving(TargetTransformInfo *TTI) const;

  // Generate vector code from the packs
  void codegen(
      IntrinsicBuilder &Builder,
      DenseMap<BasicBlock *, std::unique_ptr<LocalDependenceAnalysis>> &LDAs);
};

struct MCMCVectorPackSet : public VectorPackSet {
  void removeRandomPack();
};

// Mapping a load/store -> a set of consecutive loads/stores
//
// This is basically a generalization of a store/load chain.
// We use a DAG because a load, for example, might have multiple
// "next" candidate.
using ConsecutiveAccessDAG =
    DenseMap<Instruction *, SmallPtrSet<Instruction *, 4>>;

} // end anonymous namespace

// Do a quadratic search to build the access dags
void buildAccessDAG(ConsecutiveAccessDAG &DAG, ArrayRef<Instruction *> Accesses,
                    const DataLayout *DL, ScalarEvolution *SE) {
  for (auto *A1 : Accesses)
    for (auto *A2 : Accesses)
      if (A1->getType() == A2->getType() &&
          isConsecutiveAccess(A1, A2, *DL, *SE))
        DAG[A1].insert(A2);
};

// Get the vector value representing `OpndPack'.
// If `OpndPack` is not directly produced by another Pack,
// we need to emit code to either swizzle it together.
Value *VectorPackSet::gatherOperandPack(VectorPack::OperandPack OpndPack,
                                        const ValueIndexTy &ValueIndex,
                                        const PackToValueTy &MaterializedPacks,
                                        IntrinsicBuilder &Builder) {
  struct GatherEdge {
    unsigned SrcIndex;
    unsigned DestIndex;
  };

  std::map<const VectorPack *, SmallVector<GatherEdge, 4>> SrcPacks;
  std::map<Value *, SmallVector<unsigned, 4>> SrcScalars;

  // Figure out sources of the values in `OpndPack`
  unsigned NumValues = OpndPack.size();
  for (unsigned i = 0; i < NumValues; i++) {
    auto *V = OpndPack[i];
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

  // 1) Emit hte partial gathers
  struct PartialGather {
    BitVector DefinedBits;
    Value *Gather;
  };
  std::vector<PartialGather> PartialGathers;

  for (auto &KV : SrcPacks) {
    auto *SrcVP = KV.first;
    auto &GatherEdges = KV.second;

    BitVector DefinedBits;
    // Figure out which values we want to gather
    ShuffleMaskTy MaskValues = Undefs;
    for (auto &GE : GatherEdges) {
      MaskValues[GE.DestIndex] = ConstantInt::get(Int32Ty, GE.SrcIndex);
      DefinedBits.set(GE.DestIndex);
    }

    auto *Src = MaterializedPacks.lookup(SrcVP);
    auto *Mask = ConstantVector::get(MaskValues);
    Value *Gather;
    // Minor optimization: avoid unnecessary shuffle.
    if (SrcVP->numElements() == NumValues &&
        ShuffleVectorInst::isIdentityMask(Mask))
      Gather = Src;
    else
      Gather = Builder.CreateShuffleVector(Src, UndefValue::get(Src->getType()),
                                           Mask);

    PartialGathers.push_back({DefinedBits, Gather});
  }

  // 2) Merge the partial gathers
  auto DefinedBits = std::move(PartialGathers.back().DefinedBits);
  auto *Acc = PartialGathers.back().Gather;
  PartialGathers.pop_back();
  while (PartialGathers.empty()) {
    auto &PG = PartialGathers.back();

    ShuffleMaskTy Mask = Undefs;
    // Select from Acc
    for (unsigned Idx : DefinedBits.set_bits())
      Mask[Idx] = ConstantInt::get(Int32Ty, Idx);
    // Select from the partial gather
    for (unsigned Idx : PG.DefinedBits.set_bits())
      Mask[Idx] = ConstantInt::get(Int32Ty, NumValues + Idx);
    Acc =
        Builder.CreateShuffleVector(Acc, PG.Gather, ConstantVector::get(Mask));

    DefinedBits |= PG.DefinedBits;
    PartialGathers.pop_back();
  }

  // 3) Insert the scalar values
  for (auto &KV : SrcScalars) {
    Value *V = KV.first;
    auto &Indices = KV.second;
    for (unsigned Idx : Indices)
      Acc = Builder.CreateInsertElement(Acc, V, Idx);
  }

  return Acc;
}

bool VectorPackSet::tryAdd(BasicBlock *BB, VectorPack VP) {
  auto &Packed = PackedValues[BB];
  // Abort if one of the value we want to produce is produced by another pack
  if (Packed.anyCommon(VP.getElements()))
    return false;

  Packed |= VP.getElements();

  auto &BBPacks = Packs[BB];
  for (auto &VP2 : BBPacks) {
    // Abort if adding this pack creates circular dependence
    if (VP2.getDepended().anyCommon(VP.getElements()) &&
        VP.getElements().anyCommon(VP2.getDepended()))
      return false;
  }

  BBPacks.push_back(VP);
  return true;
}

int VectorPackSet::getCostSaving(TargetTransformInfo *TTI) const {
  int CostSaving = 0;
  // Compute arithmetic cost saving
  for (auto BBAndPacks : Packs) {
    for (auto &VP : BBAndPacks.second) {
      // FIXME: this is undercounting for more general vector instruction
      // (e.g., fmadd)
      for (Value *V : VP.elementValues()) {
        CostSaving -= TTI->getInstructionCost(cast<Instruction>(V),
                                              TargetTransformInfo::TCK_Latency);
      }
      CostSaving += VP.getProducer()->getCost(TTI, F->getContext());
    }
  }

  // TODO
  // Update the required shuffles and vector
  // First, figure out which packs we need to explicitly introduce

  return CostSaving;
}

void VectorPackSet::codegen(
    IntrinsicBuilder &Builder,
    DenseMap<BasicBlock *, std::unique_ptr<LocalDependenceAnalysis>> &LDAs) {
  ValueIndexTy ValueIndex;
  PackToValueTy MaterializedPacks;

  std::vector<Instruction *> DeadInsts;

  // Generate code in RPO of the CFG
  ReversePostOrderTraversal<Function *> RPO(F);
  for (BasicBlock *BB : RPO) {
    // Determine the schedule according to the dependence constraint
    std::vector<const VectorPack *> OrderedPacks =
        sortPacksAndScheduleBB(BB, Packs[BB], *LDAs[BB]);

    // Now generate code according to the schedule
    for (auto *VP : OrderedPacks) {
      // Get the operands ready.
      SmallVector<Value *, 2> Operands;
      unsigned OperandId = 0;
      for (auto &OpndPack : VP->getOperandPacks()) {
        VP->setOperandGatherPoint(OperandId, Builder);
        Operands.push_back(gatherOperandPack(OpndPack, ValueIndex,
                                             MaterializedPacks, Builder));
        OperandId++;
      }

      Instruction *PackLeader = cast<Instruction>(*VP->elementValues().begin());
      Builder.SetInsertPoint(PackLeader);

      // Now we can emit the vector instruction
      auto *VecInst = VP->emit(Operands, Builder);

      // Conservatively extract all elements.
      // Let the later cleanup passes clean up dead extracts.
      if (!isa<StoreInst>(VecInst)) {
        unsigned LaneId = 0;
        for (auto *V : VP->elementValues()) {
          auto *Extract = Builder.CreateExtractElement(VecInst, LaneId++);
          V->replaceAllUsesWith(Extract);
        }
      }

      // Mark the packed values as dead so we can delete them later
      for (auto *V : VP->elementValues())
        DeadInsts.push_back(cast<Instruction>(V));

      // Update the value index
      // to track where the originally scalar values are produced
      unsigned i = 0;
      for (auto *V : VP->elementValues())
        ValueIndex[V] = {VP, i++};
      // Map the pack to its materialized value
      MaterializedPacks[VP] = VecInst;
    }
  }

  // Delete the dead instructions.
  // Do it the reverse of program order to avoid dangling pointer.
  for (auto I = DeadInsts.rbegin(), E = DeadInsts.rend(); I != E; ++E)
    (*I)->eraseFromParent();
}

IRVectorBinding IRVectorBinding::Create(const BinaryIROperation *Op,
                                        unsigned VectorWidth) {
  // Compute the signature of this BINARY vector inst
  InstSignature Sig = {// bitwidths of the inputs
                       {VectorWidth, VectorWidth},
                       // bitwidth of the output
                       {VectorWidth},
                       // has imm8?
                       false};

  unsigned ElemWidth = Op->getBitwidth();
  assert(VectorWidth % ElemWidth == 0);
  unsigned NumLanes = VectorWidth / ElemWidth;
  std::vector<BoundOperation> LaneOps;
  for (int i = 0; i < NumLanes; i++) {
    unsigned Lo = i * ElemWidth, Hi = Lo + ElemWidth;
    LaneOps.push_back(BoundOperation(Op,
                                     // input binding
                                     {{0, Lo, Hi}, {1, Lo, Hi}}));
  }

  return IRVectorBinding(Op, Op->getName(), Sig, LaneOps);
}

Value *IRVectorBinding::emit(llvm::ArrayRef<llvm::Value *> Operands,
                             IntrinsicBuilder &Builder) const {
  assert(Operands.size() == 2);
  Instruction::BinaryOps Opcode = Op->getOpcode();
  return Builder.CreateBinOp(Opcode, Operands[0], Operands[1]);
}

VectorPack
VectorPackContext::createVectorPack(std::vector<Operation::Match> Matches,
                                    BitVector Elements, BitVector Depended,
                                    const InstBinding *Producer) {
  return VectorPack(this, Matches, Elements, Depended, Producer);
}

VectorPack VectorPackContext::createLoadPack(ArrayRef<LoadInst *> Loads,
                                             BitVector Elements,
                                             BitVector Depended) {
  return VectorPack(this, Loads, Elements, Depended);
}

VectorPack VectorPackContext::createStorePack(ArrayRef<StoreInst *> Stores,
                                              BitVector Elements,
                                              BitVector Depended) {
  return VectorPack(this, Stores, Elements, Depended);
}

VectorPack VectorPackContext::createPhiPack(ArrayRef<PHINode *> PHIs) {
  BitVector Elements(getNumValues());
  for (auto *PHI : PHIs)
    Elements.set(getScalarId(PHI));
  return VectorPack(this, PHIs, Elements, BitVector(getNumValues()));
}

char GSLP::ID = 0;

// Sample an integer between 0 and N.
static unsigned randint(int N) { return std::rand() % N; }

// sample indenpdent, consecutive memory accesses
template <typename MemAccessTy>
static std::tuple<std::vector<MemAccessTy *>, BitVector, BitVector>
sampleAccesses(const ConsecutiveAccessDAG &DAG, VectorPackContext &VPCtx,
               LocalDependenceAnalysis &LDA, unsigned MaxNumAccesses) {
  // Pick a seed to start the chain
  auto DAGIt = std::next(DAG.begin(), randint(DAG.size()));
  auto *LastAccess = cast<MemAccessTy>(DAGIt->first);
  auto *NextAccesses = &DAGIt->second;
  BitVector Elements(VPCtx.getNumValues());
  Elements.set(VPCtx.getScalarId(LastAccess));
  BitVector Depended = LDA.getDepended(LastAccess);

  std::vector<MemAccessTy *> Accesses{LastAccess};
  while (Accesses.size() < MaxNumAccesses) {
    assert(Elements.size() == Accesses.size());

    // Find independent candidate to extend this chain of loads
    SmallVector<MemAccessTy *, 4> IndependentAccesses;
    for (auto *L : *NextAccesses) {
      auto Depended2 = LDA.getDepended(L);
      unsigned AccessId = VPCtx.getScalarId(L);
      if (Elements.anyCommon(Depended2) || Depended.test(AccessId))
        continue;
      IndependentAccesses.push_back(cast<MemAccessTy>(L));
    }

    // Abort if we don't have anything to choose from
    if (IndependentAccesses.empty())
      break;

    // Sample one of the candidates
    LastAccess = IndependentAccesses[randint(IndependentAccesses.size())];
    Accesses.push_back(LastAccess);
    Depended |= LDA.getDepended(LastAccess);
    Elements.set(VPCtx.getScalarId(LastAccess));

    auto It = DAG.find(LastAccess);
    // This load doesn't have any consecutive load that follows
    if (It == DAG.end())
      break;
    NextAccesses = &It->second;
  }

  return {Accesses, Elements, Depended};
}

static VectorPack sampleLoadPack(
    ConsecutiveAccessDAG &LoadDAG,
    VectorPackContext &VPCtx,
    LocalDependenceAnalysis &LDA,
    unsigned MaxNumLoads) {
  std::vector<LoadInst *> Loads;
  BitVector Elements;
  BitVector Depended;
  std::tie(Loads, Elements, Depended) =
    sampleAccesses<LoadInst>(LoadDAG, VPCtx, LDA, MaxNumLoads);
  return VPCtx.createLoadPack(Loads, Elements, Depended);
}

static VectorPack sampleStorePack(
    ConsecutiveAccessDAG &StoreDAG,
    VectorPackContext &VPCtx,
    LocalDependenceAnalysis &LDA,
    unsigned MaxNumStores) {
  std::vector<StoreInst *> Stores;
  BitVector Elements;
  BitVector Depended;
  std::tie(Stores, Elements, Depended) =
    sampleAccesses<StoreInst>(StoreDAG, VPCtx, LDA, MaxNumStores);
  return VPCtx.createStorePack(Stores, Elements, Depended);
}

static VectorPack samplePhiPack(VectorPackContext &VPCtx,
                                 unsigned MaxNumPHIs) {
  // All phi nodes within a basic block are always locally independent
  // so we don't need to query the dependence analysis.

  auto *BB = VPCtx.getBasicBlock();

  // Group the phi nodes by their types
  DenseMap<Type *, SmallVector<PHINode *, 4>> PHIs;
  for (auto &PHI : BB->phis())
    PHIs[PHI.getType()].push_back(&PHI);

  // Now choose one group of isomorphic phis
  auto It = std::next(PHIs.begin(), randint(PHIs.size()));
  auto &IsoPHIs = It->second;
  // Shuffle these phis before we pack them
  std::random_shuffle(IsoPHIs.begin(), IsoPHIs.end(), randint);
  unsigned NumPHIs = std::min<unsigned>(IsoPHIs.size(), MaxNumPHIs);
  std::vector<PHINode *> SelectedPHIs(IsoPHIs.begin(),
                                      std::next(IsoPHIs.begin(), NumPHIs));
  return VPCtx.createPhiPack(SelectedPHIs);
}

// TODO: support NOOP lanes
//
// return true if success
static bool sampleGeneralPack(
    const MatchManager &MM,
    VectorPackContext &VPCtx,
    LocalDependenceAnalysis &LDA,
    InstBinding *Inst,
    VectorPack &VP, unsigned NumTrials) {

  while (NumTrials--) {
    BitVector Elements(VPCtx.getNumValues());
    BitVector Depended(VPCtx.getNumValues());

    // Fill each lane...
    bool Success = true;
    std::vector<Operation::Match> Matches;
    for (auto &LaneOp : Inst->getLaneOps()) {
      std::vector<const Operation::Match *> IndependentMatches;
      for (auto &M : MM.getMatches(LaneOp.getOperation())) {
        unsigned OutputId = VPCtx.getScalarId(M.Output);
        auto Depended2 = LDA.getDepended(cast<Instruction>(M.Output));
        // make sure M is independent from the existing values
        if (!Depended.test(OutputId) /* selcted values depends on this one */
            && !Elements.anyCommon(Depended2) /* this one depends on selected values */)
          IndependentMatches.push_back(&M);
      }
      if (IndependentMatches.empty()) {
        Success = false;
        break;
      }
      // Choose one of the independent mathes
      auto *SelectedM = IndependentMatches[randint(IndependentMatches.size())];
      Elements.set(VPCtx.getScalarId(SelectedM->Output));
      Depended |= LDA.getDepended(cast<Instruction>(SelectedM->Output));
      Matches.push_back(*SelectedM);
    }

    VP = VPCtx.createVectorPack(Matches, Elements, Depended, Inst);
    return true;
  }

  return false;
}

bool GSLP::runOnFunction(Function &F) {
  auto *AA = &getAnalysis<AAResultsWrapperPass>().getAAResults();
  auto *SE = &getAnalysis<ScalarEvolutionWrapperPass>().getSE();
  auto *TTI = &getAnalysis<TargetTransformInfoWrapperPass>().getTTI(F);

  auto *DL = &F.getParent()->getDataLayout();

  std::vector<VectorPackContext> VPCtxs;

  DenseMap<BasicBlock *, MatchManager> MMs;
  DenseMap<BasicBlock *, std::unique_ptr<LocalDependenceAnalysis>> LDAs;
  DenseMap<BasicBlock *, std::unique_ptr<ConsecutiveAccessDAG>> LoadDAGs;
  DenseMap<BasicBlock *, std::unique_ptr<ConsecutiveAccessDAG>> StoreDAGs;

  // Setup analyses and determine search space
  for (auto &BB : F) {
    std::vector<Instruction *> Loads;
    std::vector<Instruction *> Stores;
    // Find packable instructions
    auto &MM = MMs[&BB] = MatchManager(VecBindingTable.getBindings());
    for (auto &I : BB) {
      MM.match(&I);
      if (isa<LoadInst>(&I))
        Loads.push_back(&I);
      else if (isa<StoreInst>(&I))
        Stores.push_back(&I);
    }

    VPCtxs.emplace_back(&BB);
    auto &VPCtx = VPCtxs.back();
    LDAs[&BB] = std::make_unique<LocalDependenceAnalysis>(AA, &BB, VPCtx);
    auto LoadDAG = std::make_unique<ConsecutiveAccessDAG>();
    auto StoreDAG = std::make_unique<ConsecutiveAccessDAG>();
    buildAccessDAG(*LoadDAG, Loads, DL, SE);
    buildAccessDAG(*StoreDAG, Stores, DL, SE);
    LoadDAGs[&BB] = std::move(LoadDAG);
    StoreDAGs[&BB] = std::move(StoreDAG);
  }

  VectorPackSet Packs(&F);

  std::srand(42);

  IntrinsicBuilder Builder(*InstWrappers);
  Packs.codegen(Builder, LDAs);

  assert(!verifyFunction(F));
  return true;
}

INITIALIZE_PASS_BEGIN(GSLP, "gslp", "gslp", false, false)
INITIALIZE_PASS_DEPENDENCY(ScalarEvolutionWrapperPass)
INITIALIZE_PASS_DEPENDENCY(AAResultsWrapperPass)
INITIALIZE_PASS_DEPENDENCY(TargetTransformInfoWrapperPass)
INITIALIZE_PASS_END(GSLP, "gslp", "gslp", false, false)

// Automatically enable the pass.
// http://adriansampson.net/blog/clangpass.html
static void registerGSLP(const PassManagerBuilder &PMB,
                         legacy::PassManagerBase &MPM) {
  MPM.add(new GSLP());

  // run the cleanup passes, copied from llvm's pass builder
  MPM.add(createInstructionCombiningPass(true /*expensive combines*/));
  MPM.add(createLoopUnrollPass(2 /*opt level*/, PMB.DisableUnrollLoops,
                               PMB.ForgetAllSCEVInLoopUnroll));
  if (!PMB.DisableUnrollLoops) {
    MPM.add(createInstructionCombiningPass(true /*expensive combines*/));
    MPM.add(
        createLICMPass(PMB.LicmMssaOptCap, PMB.LicmMssaNoAccForPromotionCap));
  }
  MPM.add(createAlignmentFromAssumptionsPass());
  MPM.add(createLoopSinkPass());
  MPM.add(createInstSimplifyLegacyPass());
  MPM.add(createDivRemPairsPass());
  MPM.add(createCFGSimplificationPass());
}

// Register this pass to run after all optimization,
// because we want this pass to replace LLVM SLP.
static RegisterStandardPasses
    RegisterMyPass(PassManagerBuilder::EP_OptimizerLast, registerGSLP);
