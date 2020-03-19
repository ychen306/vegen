#include "InstSema.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/MemoryLocation.h"
#include "llvm/Analysis/OrderedBasicBlock.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/Analysis/VectorUtils.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"
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
// For pass building
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/InstCombine/InstCombine.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/InstSimplifyPass.h"
#include "llvm/Transforms/Vectorize.h"
#include <set>

using namespace llvm;
using namespace PatternMatch;

cl::opt<std::string> InstWrappersPath("inst-wrappers",
                                      cl::desc("Path to InstWrappers.bc"),
                                      cl::Required);
cl::opt<bool> UseMainlineSLP("use-slp",
    cl::desc("Use LLVM SLP"),
    cl::init(false));

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
    return TTI->getArithmeticInstrCost(Opcode, VecTy);
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
    AU.addRequired<BlockFrequencyInfoWrapperPass>();
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
    Instruction::BinaryOps::Or,   Instruction::BinaryOps::Xor
};

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
    for (auto &Op : VectorizableOps) {
      for (unsigned VB : VectorBitwidths) {
        // Skip singleton pack
        if (VB / Op.getBitwidth() == 1)
          continue;
        VectorInsts.emplace_back(IRVectorBinding::Create(&Op, VB));
      }
    }

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

  bool isKnownValue(const Value *V) const {
    auto It = std::lower_bound(Scalars.begin(), Scalars.end(), V);
    return It != Scalars.end() && Scalars[It - Scalars.begin()] == V;
  }

  unsigned getScalarId(const Value *V) const {
    auto It = std::lower_bound(Scalars.begin(), Scalars.end(), V);
    assert(cast<Instruction>(V)->getParent() == BB);
    assert(It != Scalars.end());
    assert(Scalars[It - Scalars.begin()] == V);
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
    Value *operator*() const {
      unsigned Id = *Handle;
      return VPCtx->getScalar(Id);
    }

    value_iterator &operator++() {
      ++Handle;
      return *this;
    }

    bool operator!=(const value_iterator &It) { return Handle != It.Handle; }
  };

  iterator_range<value_iterator> iter_values(const BitVector &Ids) const {
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
  VectorPackContext *VPCtx;
  // mapping an instruction -> instructions that it transitively depends on
  std::map<Instruction *, BitVector> TransitiveClosure;

public:
  LocalDependenceAnalysis(AliasAnalysis *AA, BasicBlock *BB,
                          VectorPackContext *VPCtx)
      : BB(BB), VPCtx(VPCtx) {
    std::vector<Instruction *> MemRefs;
    // Build the local dependence graph
    for (Instruction &I : *BB) {
      // PHINodes do not introduce any local dependence
      if (isa<PHINode>(&I))
        continue;

      for (Value *Operand : I.operands()) {
        if (auto *I2 = dyn_cast<Instruction>(Operand)) {
          if (!isa<PHINode>(I2) && I2->getParent() == BB) {
            Dependencies[&I].push_back(I2);
          }
        }
      }
      if (I.mayReadOrWriteMemory()) {
        MemoryLocation Loc = getLocation(&I, AA);
        // check dependence with preceding loads and stores
        for (auto *PrevRef : MemRefs) {
          if ((PrevRef->mayWriteToMemory() || I.mayWriteToMemory()) &&
              isAliased(Loc, &I, PrevRef, AA))
            Dependencies[&I].push_back(PrevRef);
        }
        MemRefs.push_back(&I);
      }
    }

#ifndef NDEBUG
    // Cycle detection
    DenseSet<Instruction *> Processing;
    DenseSet<Instruction *> Visited;
    std::function<void (Instruction *)> Visit = [&](Instruction *I){
      assert(!Processing.count(I) && "CYCLE DETECTED IN DEP GRAPH");
      bool Inserted = Visited.insert(I).second;
      if (!Inserted)
        return;
      Processing.insert(I);
      for (auto *Src : Dependencies[I])
        Visit(Src);
      Processing.erase(I);
    };
    for (auto &I : *BB)
      Visit(&I);
#endif

    // Now compute transitive closure in topological order,
    // which we don't need to compute because the basic block order is a valid one
    for (auto &I : *BB) {
      BitVector Depended = BitVector(VPCtx->getNumValues());
      for (auto *Src : Dependencies[&I]) {
        assert(TransitiveClosure.count(Src));
        Depended.set(VPCtx->getScalarId(Src));
        unsigned Count = Depended.count();
        Depended |= TransitiveClosure[Src];
      }

      TransitiveClosure[&I] = Depended;
    }
  }

  BitVector getDepended(Instruction *I) const {
    auto It = TransitiveClosure.find(I);
    assert(It != TransitiveClosure.end());
    return It->second;
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

  // FIXME just make VectorPack an interface
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

public:
  VectorPack(const VectorPack &Other) = default;
  VectorPack &operator=(const VectorPack &Other) = default;

  const InstBinding *getProducer() const { 
    return (Kind == General) ? Producer : nullptr;
  }

  const VectorPackContext *getContext() const { return VPCtx; }

  iterator_range<VectorPackContext::value_iterator> elementValues() const {
    return VPCtx->iter_values(Elements);
  }

  iterator_range<VectorPackContext::value_iterator> dependedValues() const {
    return VPCtx->iter_values(Depended);
  }

  BasicBlock *getBasicBlock() const { return VPCtx->getBasicBlock(); }

  std::vector<Value *> getOrderedValues() const;

  unsigned numElements() const { return Elements.count(); }

  const BitVector &getDepended() const { return Depended; }

  const BitVector &getElements() const { return Elements; }

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

  int getCost(TargetTransformInfo *TTI, LLVMContext &Ctx) const {
    switch (Kind) {
    case General:
      return Producer->getCost(TTI, Ctx);
    case Load: {
                 auto *LI = Loads[0];
                 MaybeAlign Alignment(LI->getAlignment());
                 auto *VecTy = VectorType::get(LI->getType(), Loads.size());
                 return TTI->getMemoryOpCost(Instruction::Load,
                     VecTy, Alignment, 0, LI);
               }
    case Store: {
                 auto *SI = Stores[0];
                 MaybeAlign Alignment(SI->getAlignment());
                 auto *VecTy = VectorType::get(SI->getValueOperand()->getType(), Stores.size());
                 return TTI->getMemoryOpCost(Instruction::Store,
                     VecTy, Alignment, 0, SI);
                }
    case Phi:
      return 0;
    }
  }

  // Choose a right place to gather an operand
  void setOperandGatherPoint(unsigned OperandId,
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

  void dump(raw_ostream &OS) const {
    OS << "PACK : <\n";
    for (auto *V : getOrderedValues())
      OS << *V << '\n';
    OS << ">\n";
  }
};

// Topsort the vector packs.
// Also reschedule the basic block according to the sorted packs.
//
// This reordering makes codegen easier because we can
// just insert the vector instruction immediately after the last
// instruction that you are replacing.
static std::vector<const VectorPack *>
sortPacksAndScheduleBB(BasicBlock *BB, ArrayRef<VectorPack *> Packs,
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
      for (auto *V : VP->getOrderedValues())
        ReorderedInsts.push_back(cast<Instruction>(V));
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

class VectorPackSet {
protected:
  unsigned NumPacks;
  Function *F;
  std::vector<std::unique_ptr<VectorPack>> AllPacks;
  // FIXME : rename Packs to BB2Packs;
  DenseMap<BasicBlock *, std::vector<VectorPack *>> Packs;
  DenseMap<BasicBlock *, BitVector> PackedValues;

  // This tells us where a value is located in a pack
  struct VectorPackIndex {
    const VectorPack *VP;
    unsigned Idx;

    bool operator<(const VectorPackIndex &Other) const {
      return std::tie(VP, Idx) < std::tie(Other.VP, Other.Idx);
    }
  };

  // Mapping a value to the pack that produce them.
  using ValueIndexTy = DenseMap<const Value *, VectorPackIndex>;
  // Mapping VectorPack -> their materialized values.
  using PackToValueTy = DenseMap<const VectorPack *, Value *>;

  // Get the vector value representing OpndPack.
  static Value *gatherOperandPack(const VectorPack::OperandPack &OpndPack,
                                  const ValueIndexTy &ValueIndex,
                                  const PackToValueTy &MaterializedPacks,
                                  IntrinsicBuilder &Builder);

public:
  VectorPackSet(Function *F) : NumPacks(0), F(F) {}

  unsigned getNumPacks() const { return NumPacks; }

  // Add VP to this set if it doesn't conflict with existing packs.
  // return if successful
  bool tryAdd(VectorPack VP, LocalDependenceAnalysis &LDA);

  // Remove the one we just add
  void pop();

  // Estimate cost of this pack
  float getCostSaving(TargetTransformInfo *TTI, BlockFrequencyInfo *BFI) const;

  // Generate vector code from the packs
  void codegen(
      IntrinsicBuilder &Builder,
      DenseMap<BasicBlock *, std::unique_ptr<LocalDependenceAnalysis>> &LDAs);
};

struct MCMCVectorPackSet : public VectorPackSet {
  MCMCVectorPackSet(Function *F) : VectorPackSet(F) {}
  std::unique_ptr<VectorPack> removeRandomPack();
};

// Mapping a load/store -> a set of consecutive loads/stores
//
// This is basically a generalization of a store/load chain.
// We use a DAG because a load, for example, might have multiple
// "next" candidate.
using ConsecutiveAccessDAG =
    DenseMap<Instruction *, SmallPtrSet<Instruction *, 4>>;

bool isScalarType(Type *Ty) { return Ty->getScalarType() == Ty; }

} // end anonymous namespace

std::vector<Value *> VectorPack::getOrderedValues() const {
  std::vector<Value *> OrderedValues;
  switch (Kind) {
  case General:
    for (auto &M : Matches)
      OrderedValues.push_back(M.Output);
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

// Do a quadratic search to build the access dags
template <typename MemAccessTy>
void buildAccessDAG(ConsecutiveAccessDAG &DAG, ArrayRef<MemAccessTy *> Accesses,
                    const DataLayout *DL, ScalarEvolution *SE) {
  for (auto *A1 : Accesses) {
    // Get type of the value being acccessed
    auto *Ty =
        cast<PointerType>(A1->getPointerOperand()->getType())->getElementType();
    if (!isScalarType(Ty))
      continue;
    for (auto *A2 : Accesses) {
      if (A1->getType() == A2->getType() &&
          isConsecutiveAccess(A1, A2, *DL, *SE))
        DAG[A1].insert(A2);
    }
  }
};

// Get the vector value representing `OpndPack'.
// If `OpndPack` is not directly produced by another Pack,
// we need to emit code to either swizzle it together.
Value *VectorPackSet::gatherOperandPack(const VectorPack::OperandPack &OpndPack,
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
  const unsigned NumValues = OpndPack.size();
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

  // 1) Emit hte partial gathers
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
    if (SrcVP->numElements() == NumValues &&
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
    auto *VecTy = VectorType::get(OpndPack[0]->getType(), OpndPack.size());
    Acc = UndefValue::get(VecTy);
  }

  // 3) Insert the scalar values
  for (auto &KV : SrcScalars) {
    Value *V = KV.first;
    auto &Indices = KV.second;
    for (unsigned Idx : Indices)
      Acc = Builder.CreateInsertElement(Acc, V, Idx, "gslp.insert");
  }

  return Acc;
}

bool VectorPackSet::tryAdd(VectorPack VP, LocalDependenceAnalysis &LDA) {
  auto *BB = VP.getBasicBlock();
  auto &Packed = PackedValues[BB];
  // Abort if one of the value we want to produce is produced by another pack
  if (Packed.anyCommon(VP.getElements()))
    return false;
  
  // FIXME: make this data structure part of VectorPackSet to avoid recomputing
  // Mapping values to where they are packed
  DenseMap<Value *, const VectorPack *> ValueToPackMap;
  auto &BBPacks = Packs[BB];
  for (auto *VP2 : BBPacks) {
    for (Value *V : VP2->elementValues())
      ValueToPackMap[V] = VP2;
  }

  SmallPtrSet<Value *, 8> NewValues;
  for (auto *V : VP.elementValues())
    NewValues.insert(V);

  // Do a DFS on the dependence graph starting from VP.
  // We want to see if we can get back to any of VP's values
  std::vector<const VectorPack *> Worklist {&VP};
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

  Packed |= VP.getElements();
  AllPacks.push_back(std::make_unique<VectorPack>(VP));
  BBPacks.push_back(AllPacks.back().get());
  NumPacks++;
  return true;
}

void VectorPackSet::pop() {
  auto &VP = AllPacks.back();
  auto *BB = VP->getBasicBlock();
  assert(Packs[BB].back() == VP.get());
  Packs[BB].pop_back();
  AllPacks.pop_back();
  NumPacks--;
}

static float getBlockWeight(BasicBlock *BB, BlockFrequencyInfo *BFI) {
  return float(BFI->getBlockFreq(BB).getFrequency()) / float(BFI->getEntryFreq());
}

float VectorPackSet::getCostSaving(TargetTransformInfo *TTI, BlockFrequencyInfo *BFI) const {
  int CostSaving = 0;
  assert(AllPacks.size() == NumPacks);
  // Compute arithmetic cost saving
  for (auto &VP : AllPacks) {
    auto *BB = VP->getBasicBlock();
    float BBCostSaving = 0;
    // FIXME: this is undercounting for more general vector instruction
    // (e.g., fmadd)
    for (Value *V : VP->elementValues()) {
      BBCostSaving -= TTI->getInstructionCost(cast<Instruction>(V),
          TargetTransformInfo::TCK_RecipThroughput);
    }
    BBCostSaving += VP->getCost(TTI, F->getContext());

    CostSaving += BBCostSaving * getBlockWeight(BB, BFI);
  }

  // Update cost to consider shuffles

  // First figure out which values are now in vectors
  ValueIndexTy ValueIndex;
  for (auto &VP : AllPacks) {
    unsigned i = 0;
    for (auto *V : VP->getOrderedValues())
      ValueIndex[V] = {VP.get(), i++};
  }

  const int GatherCost = 2;
  const int InsertCost = 2;
  const int PermuteCost = 1;

  // FIXME:
  // use of block frequency is pessimistic when we can hoist gathers out of loops
  for (auto &VP : AllPacks) {
    auto *BB = VP->getBasicBlock();
    float BBCost = 0;
    for (auto &OpndPack : VP->getOperandPacks()) {
      // figure out from where we need to gather
      SmallPtrSet<Value *, 4> SrcScalars;
      SmallPtrSet<const VectorPack *, 4> SrcPacks;
      for (Value *V : OpndPack) {
        auto It = ValueIndex.find(V);
        if (It != ValueIndex.end()) {
          auto &VPIdx = It->second;
          SrcPacks.insert(VPIdx.VP);
        } else {
          SrcScalars.insert(V);
        }
      }

      unsigned NumSrcs = SrcPacks.size() + SrcScalars.size();
      if (NumSrcs > 1) {
        if (SrcPacks.size() > 0)
          BBCost += GatherCost * 2*(SrcPacks.size() - 1);
        BBCost += InsertCost * SrcScalars.size();
      } else if (!SrcPacks.empty()) {
        auto *SrcPack = *SrcPacks.begin();
        // We are selecting a subset of that pack
        if (SrcPack->getElements().count() != OpndPack.size())
          BBCost += GatherCost;
        else {
          // Now see if we need to permute
          unsigned i = 0;
          bool InOrder = true;
          for (Value *V : OpndPack) {
            auto It = ValueIndex.find(V);
            if (It == ValueIndex.end() ||
                It->second.Idx != i) {
              InOrder = false;
              break;
            }
            i++;
          }
          if (!InOrder)
            BBCost += PermuteCost;
        }
      }
    }
    CostSaving += BBCost * getBlockWeight(BB, BFI);
  }

  std::set<VectorPackIndex> Extractions;
  // Now consider scalar use of vector output
  // THIS DOES NOT WORK IN GENERAL...
  for (auto &I : make_range(inst_begin(F), inst_end(F))) {
    if (ValueIndex.count(&I))
      continue;
    for (Value *V : I.operands()) {
      auto It = ValueIndex.find(V);
      if (It != ValueIndex.end())
        Extractions.insert(It->second);
    }
  }

  const unsigned ExtractCost = 2;

  for (auto &VPIdx : Extractions) {
    auto *BB = VPIdx.VP->getBasicBlock();
    CostSaving += ExtractCost * getBlockWeight(BB, BFI);
  }

  return CostSaving;
}

// FIXME: maybe we need to do some LICM and CSE for these gathers??
// LOOK INTO SLP
void VectorPackSet::codegen(
    IntrinsicBuilder &Builder,
    DenseMap<BasicBlock *, std::unique_ptr<LocalDependenceAnalysis>> &LDAs) {
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

      Instruction *PackLeader =
          cast<Instruction>(*VP->getOrderedValues().begin());
      Builder.SetInsertPoint(PackLeader);

      // Now we can emit the vector instruction
      auto *VecInst = VP->emit(Operands, Builder);

      // Conservatively extract all elements.
      // Let the later cleanup passes clean up dead extracts.
      if (!isa<StoreInst>(VecInst)) {
        unsigned LaneId = 0;
        if (isa<PHINode>(VecInst))
          Builder.SetInsertPoint(BB->getFirstNonPHI());
        for (auto *V : VP->getOrderedValues()) {
          auto *Extract = Builder.CreateExtractElement(VecInst, LaneId++);
          V->replaceAllUsesWith(Extract);
        }
      }

      // Mark the packed values as dead so we can delete them later
      for (auto *V : VP->elementValues()) {
        DeadInsts.push_back(cast<Instruction>(V));
      }

      // Update the value index
      // to track where the originally scalar values are produced
      unsigned i = 0;
      for (auto *V : VP->getOrderedValues())
        ValueIndex[V] = {VP, i++};
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
static unsigned rand_int(int N) { return std::rand() % N; }

// Sample a float between 0 and 1
float rand_float() {
  float r = (float)rand()/(float)RAND_MAX;
  return r;
}

// sample indenpdent, consecutive memory accesses
template <typename MemAccessTy>
static std::tuple<std::vector<MemAccessTy *>, BitVector, BitVector>
sampleAccesses(const ConsecutiveAccessDAG &DAG, VectorPackContext &VPCtx,
               LocalDependenceAnalysis &LDA, unsigned MaxNumAccesses) {
  // Pick a seed to start the chain
  auto DAGIt = std::next(DAG.begin(), rand_int(DAG.size()));
  auto *LastAccess = cast<MemAccessTy>(DAGIt->first);
  auto *NextAccesses = &DAGIt->second;
  BitVector Elements(VPCtx.getNumValues());
  Elements.set(VPCtx.getScalarId(LastAccess));
  BitVector Depended = LDA.getDepended(LastAccess);

  std::vector<MemAccessTy *> Accesses{LastAccess};
  assert(Elements.count() == Accesses.size());
  while (Accesses.size() < MaxNumAccesses) {

    // Find independent candidate to extend this chain of loads
    SmallVector<MemAccessTy *, 4> IndependentAccesses;
    for (auto *A : *NextAccesses) {
      auto Depended2 = LDA.getDepended(A);
      unsigned AccessId = VPCtx.getScalarId(A);
      if (Elements.anyCommon(Depended2) || Depended.test(AccessId))
        continue;
      IndependentAccesses.push_back(cast<MemAccessTy>(A));
    }

    // Abort if we don't have anything to choose from
    if (IndependentAccesses.empty())
      break;

    // Sample one of the candidates
    LastAccess = IndependentAccesses[rand_int(IndependentAccesses.size())];
    Accesses.push_back(LastAccess);
    Depended |= LDA.getDepended(LastAccess);
    Elements.set(VPCtx.getScalarId(LastAccess));

    auto It = DAG.find(LastAccess);
    // This load doesn't have any consecutive load that follows
    if (It == DAG.end())
      break;
    NextAccesses = &It->second;
    assert(Elements.count() == Accesses.size());
  }

  return {Accesses, Elements, Depended};
}

static VectorPack sampleLoadPack(ConsecutiveAccessDAG &LoadDAG,
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

static VectorPack sampleStorePack(ConsecutiveAccessDAG &StoreDAG,
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

static VectorPack
samplePhiPack(DenseMap<Type *, SmallVector<PHINode *, 4>> &PHIs,
              VectorPackContext &VPCtx, unsigned MaxNumPHIs) {
  // NOTE: All phi nodes within a basic block are always locally independent
  // so we don't need to query the dependence analysis.

  // Now choose one group of isomorphic phis.
  auto It = std::next(PHIs.begin(), rand_int(PHIs.size()));
  auto &IsoPHIs = It->second;
  // Shuffle these phis before we pack them
  std::random_shuffle(IsoPHIs.begin(), IsoPHIs.end(), rand_int);
  unsigned NumPHIs = std::min<unsigned>(IsoPHIs.size(), MaxNumPHIs);
  std::vector<PHINode *> SelectedPHIs(IsoPHIs.begin(),
                                      std::next(IsoPHIs.begin(), NumPHIs));
  return VPCtx.createPhiPack(SelectedPHIs);
}

// TODO: support NOOP lanes
//
static Optional<VectorPack> sampleVectorPack(const MatchManager &MM,
                                             VectorPackContext &VPCtx,
                                             LocalDependenceAnalysis &LDA,
                                             const InstBinding *Inst,
                                             unsigned NumTrials) {

  while (NumTrials--) {
    BitVector Elements(VPCtx.getNumValues());
    BitVector Depended(VPCtx.getNumValues());

    // Fill each lane...
    bool Success = true;
    std::vector<Operation::Match> Matches;
    for (auto &LaneOp : Inst->getLaneOps()) {
      // Figure out available independent packs
      std::vector<const Operation::Match *> IndependentMatches;
      for (auto &M : MM.getMatches(LaneOp.getOperation())) {
        unsigned OutputId = VPCtx.getScalarId(M.Output);
        // This value has already been packed
        if (Elements.test(OutputId))
          continue;
        auto Depended2 = LDA.getDepended(cast<Instruction>(M.Output));
        // Selcted values depends on this one 
        if (Depended.test(OutputId))
          continue;
        // This one depends on selected values 
        if (Depended2.anyCommon(Elements))
          continue;
        IndependentMatches.push_back(&M);
      }
      if (IndependentMatches.empty()) {
        Success = false;
        break;
      }

      // Choose one of the independent mathes
      auto *SelectedM = IndependentMatches[rand_int(IndependentMatches.size())];
      Elements.set(VPCtx.getScalarId(SelectedM->Output));
      Depended |= LDA.getDepended(cast<Instruction>(SelectedM->Output));
      Matches.push_back(*SelectedM);
      assert(Elements.count() == Matches.size());
    }

    if (Success) {
      auto VP = VPCtx.createVectorPack(Matches, Elements, Depended, Inst);
      return VP;
    }
  }

  return None;
}

// Erase stuff from a vector when we don't care about ordering within the vector
template <typename T>
void eraseUnordered(std::vector<T> &Container, typename std::vector<T>::iterator It) {
  // first swap the stuff we want to delete to the end
  auto LastIt = std::prev(Container.end());
  std::iter_swap(It, LastIt);
  Container.pop_back();
}

std::unique_ptr<VectorPack> MCMCVectorPackSet::removeRandomPack() {
  auto It = std::next(AllPacks.begin(), rand_int(AllPacks.size()));
  auto *VP = It->get();
  auto *BB = VP->getBasicBlock();

  // Find the local iterator
  auto &LocalPacks = Packs[BB];
  auto LocalIt = std::find(LocalPacks.begin(), LocalPacks.end(), VP);
  assert(LocalIt != LocalPacks.end());

  // Delete the pack pointer from the basic block index
  eraseUnordered(LocalPacks, LocalIt);
  // Delete the pack itself
  std::unique_ptr<VectorPack> Removed(It->release());
  eraseUnordered(AllPacks, It);


  auto &Packed = PackedValues[BB];
  Packed ^= Removed->getElements();

  NumPacks--;
  return Removed;
}

bool GSLP::runOnFunction(Function &F) {
  auto *AA = &getAnalysis<AAResultsWrapperPass>().getAAResults();
  auto *SE = &getAnalysis<ScalarEvolutionWrapperPass>().getSE();
  auto *TTI = &getAnalysis<TargetTransformInfoWrapperPass>().getTTI(F);
  auto *BFI = &getAnalysis<BlockFrequencyInfoWrapperPass>().getBFI();

  auto *DL = &F.getParent()->getDataLayout();

  // FIXME: fuse all of these together into a single map
  DenseMap<BasicBlock *, std::unique_ptr<MatchManager>> MMs;
  DenseMap<BasicBlock *, std::unique_ptr<LocalDependenceAnalysis>> LDAs;
  DenseMap<BasicBlock *, std::unique_ptr<ConsecutiveAccessDAG>> LoadDAGs;
  DenseMap<BasicBlock *, std::unique_ptr<ConsecutiveAccessDAG>> StoreDAGs;
  DenseMap<BasicBlock *, std::unique_ptr<VectorPackContext>> VPCtxs;

  // Setup analyses and determine search space
  for (auto &BB : F) {
    std::vector<LoadInst *> Loads;
    std::vector<StoreInst *> Stores;
    // Find packable instructions
    auto MM = std::make_unique<MatchManager>(VecBindingTable.getBindings());
    for (auto &I : BB) {
      MM->match(&I);
      if (auto *LI = dyn_cast<LoadInst>(&I)) {
        if (LI->isSimple())
          Loads.push_back(LI);
      } else if (auto *SI = dyn_cast<StoreInst>(&I)) {
        if (SI->isSimple())
          Stores.push_back(SI);
      }
    }

    auto VPCtx = std::make_unique<VectorPackContext>(&BB);
    auto LoadDAG = std::make_unique<ConsecutiveAccessDAG>();
    auto StoreDAG = std::make_unique<ConsecutiveAccessDAG>();
    buildAccessDAG<LoadInst>(*LoadDAG, Loads, DL, SE);
    buildAccessDAG<StoreInst>(*StoreDAG, Stores, DL, SE);

    MMs[&BB] = std::move(MM);
    LDAs[&BB] = std::make_unique<LocalDependenceAnalysis>(AA, &BB, VPCtx.get());
    VPCtxs[&BB] = std::move(VPCtx);
    LoadDAGs[&BB] = std::move(LoadDAG);
    StoreDAGs[&BB] = std::move(StoreDAG);
  }

  MCMCVectorPackSet Packs(&F);
  std::srand(42);

  // First find out if which vector instruction we can emit.
  // E.g. sometimes there is simply no `fadd` in a basic block..
  DenseMap<BasicBlock *, SmallPtrSet<const InstBinding *, 4>> InstBindings;
  for (auto *Inst : VecBindingTable.getBindings()) {
    for (auto &BB : F) {
      Optional<VectorPack> VPOrNull =
        sampleVectorPack(*MMs[&BB], *VPCtxs[&BB], *LDAs[&BB], Inst, 32);
      if (VPOrNull)
        InstBindings[&BB].insert(Inst);
    }
  }

  const unsigned ProbLoad = 2;
  const unsigned ProbStore = 2;
  const unsigned ProbPhi = 1;
  const unsigned ProbGeneral = 5;

  auto sampleOnePack = [&]() -> bool {
    auto &RandInst = *std::next(inst_begin(F), rand_int(F.getInstructionCount()));
    auto *BB = RandInst.getParent();
    unsigned P = rand_int(10);
    if (P < ProbLoad) {
      auto &LoadDAG = *LoadDAGs[BB];
      if (LoadDAG.empty())
        return false;
      return Packs.tryAdd(sampleLoadPack(LoadDAG, *VPCtxs[BB], *LDAs[BB], 4),
          *LDAs[BB]);
    }
    P -= ProbLoad;

    if (P < ProbStore) {
      auto &StoreDAG = *StoreDAGs[BB];
      if (StoreDAG.empty())
        return false;
      return Packs.tryAdd(
          sampleStorePack(StoreDAG, *VPCtxs[BB], *LDAs[BB], 4),
          *LDAs[BB]);
    }
    P -= ProbStore;

    if (P < ProbPhi) {
      // FIXME: do this in a preprocessing pass
      DenseMap<Type *, SmallVector<PHINode *, 4>> PHIs;
      // Group the phi nodes by their types
      for (auto &PHI : BB->phis()) {
        if (!isScalarType(PHI.getType()))
          continue;
        PHIs[PHI.getType()].push_back(&PHI);
      }
      if (PHIs.empty())
        return false;
      return Packs.tryAdd(samplePhiPack(PHIs, *VPCtxs[BB], 4),
          *LDAs[BB]);
    }

    auto &Bindings = InstBindings[BB];
    if (Bindings.empty())
      return false;
    // FIXME: refactor all of these `std::next(... rand_int))` stuff
    auto *Inst = *std::next(Bindings.begin(), rand_int(Bindings.size()));
    Optional<VectorPack> VPOrNull =
      sampleVectorPack(*MMs[BB], *VPCtxs[BB], *LDAs[BB], Inst, 32);
    return VPOrNull && Packs.tryAdd(VPOrNull.getValue(), *LDAs[BB]);
  };

  const unsigned NumIters = 10000;
  const float Beta = 1.0;

  float Cost = 0.0;
  for (int i = 0; i < 100; i++)
    sampleOnePack();
#if 0
  for (int i = 0; i < NumIters; i++) {
    std::unique_ptr<VectorPack> Removed;
    if (Packs.getNumPacks() && rand_int(10) < 1) {
      Removed = Packs.removeRandomPack();
    } else {
    bool Changed = sampleOnePack();
    if (!Changed) continue;
    }
    float NewCost = Packs.getCostSaving(TTI, BFI);
    if (NewCost < Cost - logf(rand_float())/Beta) {
      Cost = NewCost;
    } else {
      if (Removed)
        Packs.tryAdd(Removed->getBasicBlock(), *Removed);
      else
        Packs.pop();
    }
    if (i % 100)
      errs() << "COST: " << Cost
        << ", NUM PACKS: " << Packs.getNumPacks()
        << '\n';
  }
#endif

  IntrinsicBuilder Builder(*InstWrappers);
  Packs.codegen(Builder, LDAs);

  assert(!verifyFunction(F, &errs()));
  return true;
}

INITIALIZE_PASS_BEGIN(GSLP, "gslp", "gslp", false, false)
INITIALIZE_PASS_DEPENDENCY(ScalarEvolutionWrapperPass)
INITIALIZE_PASS_DEPENDENCY(AAResultsWrapperPass)
INITIALIZE_PASS_DEPENDENCY(TargetTransformInfoWrapperPass)
INITIALIZE_PASS_DEPENDENCY(BlockFrequencyInfoWrapperPass)
INITIALIZE_PASS_END(GSLP, "gslp", "gslp", false, false)

// Automatically enable the pass.
// http://adriansampson.net/blog/clangpass.html
static void registerGSLP(const PassManagerBuilder &PMB,
                         legacy::PassManagerBase &MPM) {
  if (UseMainlineSLP) {
    errs() << "USING LLVM SLP\n";
    MPM.add(createSLPVectorizerPass());
  } else {
    errs() << "USING G-SLP\n";
    MPM.add(new GSLP());
  }

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
