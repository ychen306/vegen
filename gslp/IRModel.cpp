#include "IRModel.h"
#include "MatchManager.h"
#include "Packer.h"
#include "Solver.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/FormatVariadic.h"
#include <map>
#include <torch/nn/module.h>
#include <torch/torch.h>

using namespace llvm;
using namespace torch;

namespace {
class OpcodeTable {
  static unsigned getUnknownTypeId() { return 0; }
  static unsigned getConstId() { return 1; }
  static unsigned getCastId() { return 2; }
  static unsigned getBitwidth(llvm::Type *Ty) {
    if (auto *IntTy = dyn_cast<IntegerType>(Ty))
      return IntTy->getBitWidth();
    if (Ty->isFloatTy())
      return 32;
    if (Ty->isDoubleTy())
      return 64;
    return 0; // don't care
  }

  static std::vector<unsigned> Bitwidths;
  static std::vector<unsigned> Opcodes;
  std::map<std::pair<unsigned, unsigned>, unsigned> ValueTypeIds;

public:
  OpcodeTable() {
    for (unsigned BW : Bitwidths)
      for (unsigned Opc : Opcodes) {
        unsigned TypeId = ValueTypeIds.size();
        ValueTypeIds[{Opc, BW}] = TypeId;
      }
  }
  unsigned getNumValueTypes() const {
    // # of value types = <# inst opcode> * <# bitwidths> + <constant> + <cast>
    // <unknown>
    return Opcodes.size() * Bitwidths.size() + 1 + 1 + 1;
  }

  unsigned getValueTypeId(Value *V) const {
    if (isa<ConstantInt>(V) || isa<ConstantFP>(V))
      return getConstId();
    if (auto *I = dyn_cast<Instruction>(V)) {
      if (I->isCast())
        return getCastId();
      llvm::Type *Ty;
      if (auto *SI = dyn_cast<StoreInst>(I))
        Ty = SI->getValueOperand()->getType();
      else
        Ty = I->getType();
      auto It = ValueTypeIds.find({I->getOpcode(), getBitwidth(Ty)});
      if (It != ValueTypeIds.end())
        return It->second;
    }
    return getUnknownTypeId();
  }

} OpTable;

struct DiEdge {
  unsigned Src, Dest;
  DiEdge(unsigned S, unsigned T) : Src(S), Dest(T) {}
};

torch::Tensor buildAdjacencyMat(llvm::ArrayRef<DiEdge> Edges, unsigned N,
                                unsigned M, bool Flip = false) {
  auto CooIndices = torch::empty({2, (int64_t)Edges.size()},
                                 TensorOptions().dtype(torch::kInt64));
  for (unsigned i = 0; i < Edges.size(); i++) {
    if (Flip) {
      CooIndices[0][i] = (int64_t)Edges[i].Src;
      CooIndices[1][i] = (int64_t)Edges[i].Dest;
    } else {
      CooIndices[1][i] = (int64_t)Edges[i].Src;
      CooIndices[0][i] = (int64_t)Edges[i].Dest;
    }
  }
  return torch::sparse_coo_tensor(CooIndices,
                                  torch::ones({(int64_t)Edges.size()}), {N, M});
}
torch::Tensor buildAdjacencyMat(llvm::ArrayRef<DiEdge> Edges, unsigned N,
                                bool Flip = false) {
  return buildAdjacencyMat(Edges, N, N, Flip);
}

// Sample from a subset and return (re-normalized) log-prob of the sample
std::pair<unsigned, torch::Tensor>
sampleFromSubset(torch::Tensor Probs, std::vector<int64_t> &SubsetIndices) {
  auto Indices =
      torch::from_blob(SubsetIndices.data(), {(int64_t)SubsetIndices.size()},
                       TensorOptions().dtype(torch::kInt64))
          .clone()
          .to(Probs.device());
  auto SubsetProbs = Probs.index_select(0, Indices) + 0.001;
  auto i = torch::multinomial(SubsetProbs, 1).item<int64_t>();
  // Renormalize the probability
  auto Prob = SubsetProbs[i] / SubsetProbs.sum();
  return {SubsetIndices[i], Prob.log()};
}

template <typename OutStreamTy>
void dumpShape(torch::Tensor X, OutStreamTy &Os) {
  for (auto N : X.sizes()) {
    Os << " " << N;
  }
  Os << '\n';
}

} // end anonymous namespace

std::vector<unsigned> OpcodeTable::Bitwidths = {8, 16, 32, 64};
// TODO: support PHI
std::vector<unsigned> OpcodeTable::Opcodes = {
    /*Instruction::PHI, */ Instruction::Load,
    Instruction::Store,
    Instruction::Add,
    Instruction::FAdd,
    Instruction::Sub,
    Instruction::FSub,
    Instruction::Mul,
    Instruction::FMul,
    Instruction::UDiv,
    Instruction::SDiv,
    Instruction::FDiv,
    Instruction::URem,
    Instruction::SRem,
    Instruction::FRem,
    Instruction::Shl,
    Instruction::LShr,
    Instruction::AShr,
    Instruction::And,
    Instruction::Or,
    Instruction::Xor};

void IRIndex::trackValue(Value *V) {
  if (Value2IdMap.count(V))
    return;
  unsigned Id = Values.size();
  Values.push_back(V);
  Value2IdMap[V] = Id;
}

IRIndex::IRIndex(llvm::Function &F) {
  for (auto &I : make_range(inst_begin(F), inst_end(F))) {
    trackValue(&I);
    for (Value *Operand : I.operands())
      trackValue(Operand);
  }
}

IRIndex::IRIndex(const Frontier *Frt) {
  BasicBlock *BB = Frt->getBasicBlock();
  for (auto &I : *BB) {
    if (!Frt->isFree(&I))
      continue;
    trackValue(&I);
    for (Value *Operand : I.operands())
      trackValue(Operand);
  }
}

// u->v === v using u
static torch::Tensor buildInvUseGraph(const IRIndex &Index) {
  std::vector<DiEdge> Edges;
  unsigned N = Index.getNumValues();
  for (unsigned i = 0; i < N; i++) {
    auto *V = Index.get(i);
    auto *I = dyn_cast<Instruction>(V);
    if (!I)
      continue;
    for (Value *Operand : I->operands())
      // Value -> user
      Edges.emplace_back(Index.getValueId(Operand), Index.getValueId(I));
  }
  return buildAdjacencyMat(Edges, N);
}

// u->v === u using v
static torch::Tensor buildUseGraph1(const IRIndex &Index) {
  std::vector<DiEdge> Edges;
  unsigned N = Index.getNumValues();
  for (unsigned i = 0; i < N; i++) {
    auto *V = Index.get(i);
    auto *I = dyn_cast<Instruction>(V);
    if (!I)
      continue;
    if (I->getNumOperands() < 1)
      continue;
    Edges.emplace_back(Index.getValueId(I), Index.getValueId(I->getOperand(0)));
  }
  return buildAdjacencyMat(Edges, N);
}

// u->v === u using v
static torch::Tensor buildUseGraph2(const IRIndex &Index) {
  std::vector<DiEdge> Edges;
  unsigned N = Index.getNumValues();
  for (unsigned i = 0; i < N; i++) {
    auto *V = Index.get(i);
    auto *I = dyn_cast<Instruction>(V);
    if (!I || isa<LoadInst>(I))
      continue;
    if (I->getNumOperands() < 2)
      continue;
    Edges.emplace_back(Index.getValueId(I), Index.getValueId(I->getOperand(1)));
  }
  return buildAdjacencyMat(Edges, N);
}

static void getEdges(std::vector<DiEdge> &Edges, const IRIndex &Index,
                     ConsecutiveAccessDAG &AccessDAG) {
  for (auto &LeftAndRights : AccessDAG) {
    auto *Left = LeftAndRights.first;
    auto &Rights = LeftAndRights.second;
    unsigned LeftId = Index.getValueId(Left);
    for (auto *Right : Rights) {
      unsigned RightId = Index.getValueId(Right);
      Edges.emplace_back(LeftId, RightId);
    }
  }
}

// Having edge uv means u if to the left of v (u and v are mem refs)
static torch::Tensor buildRightMemRefGraph(
    const IRIndex &Index,
    DenseMap<BasicBlock *, std::unique_ptr<ConsecutiveAccessDAG>> &LoadDAGs,
    DenseMap<BasicBlock *, std::unique_ptr<ConsecutiveAccessDAG>> &StoreDAGs) {
  std::vector<DiEdge> Edges;
  for (auto &KV : LoadDAGs)
    getEdges(Edges, Index, *KV.second);
  for (auto &KV : StoreDAGs)
    getEdges(Edges, Index, *KV.second);
  return buildAdjacencyMat(Edges, Index.getNumValues());
}

// Having edge uv means u if to the right of v (u and v are mem refs)
static torch::Tensor buildLeftMemRefGraph(
    const IRIndex &Index,
    llvm::DenseMap<BasicBlock *, std::unique_ptr<ConsecutiveAccessDAG>>
        &LoadDAGs,
    llvm::DenseMap<BasicBlock *, std::unique_ptr<ConsecutiveAccessDAG>>
        &StoreDAGs) {
  std::vector<DiEdge> Edges;
  for (auto &KV : LoadDAGs)
    getEdges(Edges, Index, *KV.second);
  for (auto &KV : StoreDAGs)
    getEdges(Edges, Index, *KV.second);
  return buildAdjacencyMat(Edges, Index.getNumValues(), true /*flip*/);
}

// Having edge uv means u if to the left of v (u and v are mem refs)
static torch::Tensor buildRightMemRefGraph(const IRIndex &Index,
                                           ConsecutiveAccessDAG &LoadDAG,
                                           ConsecutiveAccessDAG &StoreDAG) {
  std::vector<DiEdge> Edges;
  getEdges(Edges, Index, LoadDAG);
  getEdges(Edges, Index, StoreDAG);
  return buildAdjacencyMat(Edges, Index.getNumValues());
}

// Having edge uv means u if to the right of v (u and v are mem refs)
static torch::Tensor buildLeftMemRefGraph(const IRIndex &Index,
                                          ConsecutiveAccessDAG &LoadDAG,
                                          ConsecutiveAccessDAG &StoreDAG) {
  std::vector<DiEdge> Edges;
  getEdges(Edges, Index, LoadDAG);
  getEdges(Edges, Index, StoreDAG);
  return buildAdjacencyMat(Edges, Index.getNumValues(), true /*flip*/);
}

static torch::Tensor getValueTypes(const IRIndex &Index) {
  unsigned N = Index.getNumValues();
  auto ValueTypes = torch::empty({N}, TensorOptions().dtype(torch::kInt64));
  for (unsigned i = 0; i < N; i++)
    ValueTypes[i] = (int64_t)OpTable.getValueTypeId(Index.get(i));
  return ValueTypes;
}

PackModelImpl::PackModelImpl(unsigned EmbSize,
                             llvm::ArrayRef<InstBinding *> Insts,
                             unsigned MaxNumLanes)
    : EmbSize(EmbSize), Insts(Insts) {
  // lstm : <user> x <operand 1> x <operand 2> x <left mem refs> x <right mem
  // refs> -> (h, c)
  auto GRUOpt = nn::GRUCellOptions(EmbSize * 5, EmbSize);

  // # of possible pack opcode : <no pack> + <# of general packs> + store
  // TODO: support phi and load
  unsigned NumPackOps = Insts.size() + 1 + 1;

  GRU = register_module("rnn", nn::GRUCell(GRUOpt));
  OpcodeEmb = register_module(
      "opcode_embedding",
      nn::Embedding(nn::EmbeddingOptions(OpTable.getNumValueTypes(), EmbSize)));
  StateToUserMsg = register_module("state2user", nn::Linear(EmbSize, EmbSize));
  StateToUseMsg1 = register_module("state2msg1", nn::Linear(EmbSize, EmbSize));
  StateToUseMsg2 = register_module("state2msg2", nn::Linear(EmbSize, EmbSize));
  StateToMemMsg = register_module("state2mem", nn::Linear(EmbSize, EmbSize));
  StateToEmb = register_module("state2out", nn::Linear(EmbSize, EmbSize));
  StateToNop = register_module("state2nop", nn::Linear(EmbSize, 1));
  StateToInst = register_module("state2inst", nn::Linear(EmbSize, NumPackOps));
  for (unsigned i = 0; i < MaxNumLanes; i++) {
    StateToLaneEmbs.push_back(register_module(formatv("state2lane{0}", i),
                                              nn::Linear(EmbSize, EmbSize)));
  }
}

PackDistributionDeprecated PackModelImpl::forward(
    torch::Device &Device, const IRIndex &Index,
    DenseMap<BasicBlock *, std::unique_ptr<ConsecutiveAccessDAG>> &LoadDAGs,
    DenseMap<BasicBlock *, std::unique_ptr<ConsecutiveAccessDAG>> &StoreDAGs,
    unsigned NumIters) {
  // FIXME: hoist these out
  auto InvUseGraph = buildInvUseGraph(Index).to(Device);
  auto UseGraph1 = buildUseGraph1(Index).to(Device);
  auto UseGraph2 = buildUseGraph2(Index).to(Device);
  auto LeftMemRefGraph =
      buildLeftMemRefGraph(Index, LoadDAGs, StoreDAGs).to(Device);
  auto RightMemRefGraph =
      buildRightMemRefGraph(Index, LoadDAGs, StoreDAGs).to(Device);

  unsigned N = Index.getNumValues();

  // Initialize the states
  auto ValueTypes = getValueTypes(Index).to(Device);
  auto H = OpcodeEmb->forward(ValueTypes).view({N, EmbSize});

  auto GetMessages = [&](torch::Tensor H) -> torch::Tensor {
    auto MemMsg = StateToMemMsg->forward(H);

    auto UserMsg = torch::mm(InvUseGraph, StateToUserMsg->forward(H));
    auto Msg1 = torch::mm(UseGraph1, StateToUseMsg1->forward(H));
    auto Msg2 = torch::mm(UseGraph2, StateToUseMsg2->forward(H));
    auto LeftMemMsg = torch::mm(LeftMemRefGraph, MemMsg);
    auto RightMemMsg = torch::mm(RightMemRefGraph, MemMsg);

    return torch::cat({UserMsg, Msg1, Msg2, LeftMemMsg, RightMemMsg},
                      1 /*dim*/);
  };

  for (unsigned i = 0; i < NumIters; i++)
    H = GRU->forward(GetMessages(H), H);

  auto OpProb = StateToInst->forward(H).softmax(1 /*dim*/);
  auto Emb = StateToEmb->forward(H);
  auto NopSimilarity = StateToNop->forward(H);
  std::vector<torch::Tensor> LaneProbs;
  for (auto &StateToLane : StateToLaneEmbs) {
    auto InstSimilarity = StateToLane(H).mm(Emb.t());
    LaneProbs.push_back(
        torch::cat({InstSimilarity, NopSimilarity}, 1 /*dim*/).softmax(1));
  }
  return PackDistributionDeprecated(OpProb, LaneProbs);
}

static const unsigned OpcodeNoPack = 0;
static const unsigned OpcodeStore = 1;

static const unsigned MaxNumStores = 8;

PackSample PackDistributionDeprecated::sample(
    const IRIndex &Index, Instruction *Focus,
    const VectorPackSet &ExistingPacks, llvm::ArrayRef<InstBinding *> Insts,
    DenseMap<BasicBlock *, std::unique_ptr<LocalDependenceAnalysis>> &LDAs,
    DenseMap<BasicBlock *, std::unique_ptr<ConsecutiveAccessDAG>> &LoadDAGs,
    DenseMap<BasicBlock *, std::unique_ptr<ConsecutiveAccessDAG>> &StoreDAGs,
    DenseMap<BasicBlock *, std::unique_ptr<VectorPackContext>> &VPCtxs,
    DenseMap<BasicBlock *, std::unique_ptr<MatchManager>> &MMs,
    TargetTransformInfo *TTI) const {

  unsigned FocusId = Index.getValueId(Focus);
  const unsigned NopId = Index.getNumValues();

  if (auto *SI = dyn_cast<StoreInst>(Focus)) {
    // Can't figure out how to convert a `0` literal to tensor...
    auto *BB = SI->getParent();
    auto &StoreDAG = *StoreDAGs[BB];

    // If the focus is a store then we only have two options:
    // <no pack> and <store pack>
    torch::Tensor OpLogProb;
    unsigned OpId;
    std::vector<int64_t> Options{OpcodeNoPack, OpcodeStore};
    std::tie(OpId, OpLogProb) = sampleFromSubset(OpProb[FocusId], Options);
    // We also can't pack if there are no consecutive stores next to this one.
    if (OpId == OpcodeNoPack || !StoreDAG.count(SI))
      return PackSample{nullptr, OpLogProb};

    auto &VPCtx = *VPCtxs[BB];
    auto &LDA = *LDAs[BB];

    BitVector Elements(VPCtx.getNumValues());
    BitVector Depended = LDA.getDepended(Focus);
    Elements.set(VPCtx.getScalarId(Focus));

    std::vector<StoreInst *> Stores = {SI};
    std::vector<int64_t> AvailableStores;

    torch::Tensor VPLogProb = OpLogProb;
    // Samples lanes to build a vector pack
    for (unsigned i = 0; i < MaxNumStores; i++) {
      // Find the next set of adjacent
      auto It = StoreDAG.find(SI);
      if (It == StoreDAG.end())
        break;
      auto &Next = It->second;
      AvailableStores = {NopId};
      for (auto *SI2 : Next) {
        if (!checkIndependence(LDA, VPCtx, SI2, Elements, Depended))
          continue;
        if (ExistingPacks.contains(SI2, VPCtx))
          continue;
        AvailableStores.push_back(Index.getValueId(SI2));
      }
      torch::Tensor LaneLogProb;
      unsigned InstId;
      std::tie(InstId, LaneLogProb) =
          sampleFromSubset(LaneProbs[i][FocusId], AvailableStores);
      if (InstId == NopId)
        break;
      VPLogProb = VPLogProb + LaneLogProb;
      auto *NextSI = cast<StoreInst>(Index.get(InstId));
      Stores.push_back(NextSI);
      Elements.set(VPCtx.getScalarId(NextSI));
      Depended |= LDA.getDepended(NextSI);
      SI = NextSI;
    }
    auto *VP = VPCtx.createStorePack(Stores, Elements, Depended, TTI);
    return PackSample{VP, VPLogProb};
  }

  auto *BB = Focus->getParent();
  auto &VPCtx = *VPCtxs[BB];
  auto &LDA = *LDAs[BB];
  auto &MM = *MMs[BB];

  // Sample a general vector pack
  // 1) Sample the vector opcode
  // FIXME: hoist `OpcodeIds` out. it's static
  std::vector<int64_t> OpcodeIds(Insts.size() + 1);
  OpcodeIds[0] = OpcodeNoPack;
  for (unsigned i = 0; i < Insts.size(); i++)
    // FIXME: abstract out these +2/-2 expressions
    OpcodeIds[i + 1] = i + 2;
  unsigned OpcodeId;
  torch::Tensor OpLogProb;
  std::tie(OpcodeId, OpLogProb) = sampleFromSubset(OpProb[FocusId], OpcodeIds);
  if (OpcodeId == OpcodeNoPack)
    return PackSample{nullptr, OpLogProb};

  torch::Tensor VPLogProb = OpLogProb;
  const InstBinding *Inst = Insts[OpcodeId - 2];
  // 2) Sample the lanes
  llvm::ArrayRef<BoundOperation> LaneOps = Inst->getLaneOps();
  unsigned NumLanes = LaneOps.size();
  BitVector Elements(VPCtx.getNumValues());
  BitVector Depended = LDA.getDepended(Focus);

  std::vector<int64_t> MatchOutputs;
  std::vector<const Operation::Match *> Matches;
  for (unsigned i = 0; i < NumLanes; i++) {
    // Find all of the matches we can use first.
    MatchOutputs = {NopId};
    for (auto &Match : MM.getMatches(LaneOps[i].getOperation())) {
      auto *I = cast<Instruction>(Match.Output);
      if (!checkIndependence(LDA, VPCtx, I, Elements, Depended))
        continue;
      if (ExistingPacks.contains(I, VPCtx))
        continue;
      // Focus inst must also be in the first lane
      if (i == 0 && Match.Output != Focus)
        continue;
      // FIXME: make sure `MatchOutputs` don't have duplicates
      MatchOutputs.push_back(Index.getValueId(I));
    }
    // Abort if there's no available matches
    if (MatchOutputs.empty())
      return PackSample{nullptr, VPLogProb};

    // Sample from the available matches
    unsigned InstId;
    torch::Tensor LaneLogProb;
    std::tie(InstId, LaneLogProb) =
        sampleFromSubset(LaneProbs[i][FocusId], MatchOutputs);
    VPLogProb = VPLogProb + LaneLogProb;
    // FIXME: support nop lane
    if (InstId == NopId)
      return PackSample{nullptr, VPLogProb};
    llvm::ArrayRef<Operation::Match> MatchesWithOutput =
        MM.getMatchesForOutput(LaneOps[i].getOperation(), Index.get(InstId));
    // FIXME: deal with the fact that you can have multiple matches with the
    // same output
    auto *Match = &MatchesWithOutput[0];
    Matches.push_back(Match);
    Elements.set(VPCtx.getScalarId(Match->Output));
    Depended |= LDA.getDepended(cast<Instruction>(Match->Output));
  }
  auto *VP = VPCtx.createVectorPack(Matches, Elements, Depended, Inst, TTI);
  return PackSample{VP, VPLogProb};
}

torch::Tensor PackDistributionDeprecated::entropy() const {
  std::vector<torch::Tensor> LaneEntropy;
  for (auto LaneProb : LaneProbs)
    LaneEntropy.push_back(
        torch::sum(-LaneProb.log() * LaneProb, 1 /*dim*/).mean());
  return torch::stack(LaneEntropy).mean();
}

void loadModel(PackModel &PackModel, std::string ModelPath) {
  torch::load(PackModel, ModelPath, torch::Device(torch::kCPU));
}

PackingModelImpl::PackingModelImpl(unsigned EmbSize,
                                   llvm::ArrayRef<InstBinding *> InstPool,
                                   unsigned MaxNumLanes)
    : EmbSize(EmbSize), InstPool(InstPool), MaxNumLanes(MaxNumLanes) {
  // ======= Parameters for initializing the states =======
  OpcodeEmb = register_module(
      "opcode_embedding",
      nn::Embedding(nn::EmbeddingOptions(OpTable.getNumValueTypes(), EmbSize)));
  InitUse = register_parameter("init_use", torch::randn(EmbSize));

  // ======= Message passing =======
  StateToUseMsg1 = register_module("state2msg1", nn::Linear(EmbSize, EmbSize));
  StateToUseMsg2 = register_module("state2msg2", nn::Linear(EmbSize, EmbSize));
  StateToMemMsg = register_module("state2mem", nn::Linear(EmbSize, EmbSize));
  StateToIndependentMsg =
      register_module("state2ind", nn::Linear(EmbSize, EmbSize));
  StateToUnresolvedMsg =
      register_module("state2unresolved", nn::Linear(EmbSize, EmbSize));

  UnresolvedToMsg = register_module("use2msg", nn::Linear(EmbSize, EmbSize));

  // ======= Read out =======
  // Opcode = nop + <insts from inst pool> + <stores from 2 to max vl> + <loads
  // ...>
  unsigned NumPackOps = InstPool.size() + 1 + (MaxNumLanes - 2 + 1);
  StateToOpcode =
      register_module("state2inst", nn::Linear(EmbSize, NumPackOps));
  StateToEmb = register_module("state2emb", nn::Linear(EmbSize, EmbSize));
  for (unsigned i = 0; i < MaxNumLanes; i++)
    StateToLaneEmbs.push_back(register_module(formatv("state2lane{0}", i),
                                              nn::Linear(EmbSize, EmbSize)));

  // ======= RNN for aggregating state and messages =======
  // Input = operand1 x operand2 x <left mem> x <right mem> x <independent> x
  // <unresolved use>
  ValueGRU = register_module(
      "value_gru", nn::GRUCell(nn::GRUCellOptions(EmbSize * 6, EmbSize)));
  UseGRU = register_module("use_gru", nn::GRUCell(nn::GRUCellOptions(
                                          EmbSize * MaxNumLanes, EmbSize)));
}

static torch::Tensor buildIndependenceGraph(const Frontier *Frt, Packer *Pkr,
                                            IRIndex &Index) {
  auto *BB = Frt->getBasicBlock();
  auto *VPCtx = Pkr->getContext(BB);
  auto &LDA = Pkr->getLDA(BB);

  std::vector<DiEdge> Edges;

  for (auto I = BB->begin(), E = BB->end(); I != E; ++I) {
    if (!Frt->isFree(&*I))
      continue;
    unsigned i = VPCtx->getScalarId(&*I);
    auto &Depended = LDA.getDepended(&*I);
    for (auto J = std::next(I); J != E; ++J) {
      if (!Frt->isFree(&*J))
        continue;
      unsigned j = VPCtx->getScalarId(&*J);
      if (Depended.test(j))
        continue;
      if (LDA.getDepended(&*J).test(i))
        continue;

      Edges.emplace_back(Index.getValueId(&*I), Index.getValueId(&*J));
      Edges.emplace_back(Index.getValueId(&*J), Index.getValueId(&*I));
    }
  }
  return buildAdjacencyMat(Edges, Index.getNumValues());
}

// uv means u uses v at some lane
static std::vector<torch::Tensor>
buildUnresolvedUseGraphs(const Frontier *Frt, Packer *Pkr, IRIndex &Index,
                         unsigned MaxNumLanes) {
  BasicBlock *BB = Frt->getBasicBlock();
  llvm::ArrayRef<const OperandPack *> UnresolvedPacks =
      Frt->getUnresolvedPacks();
  std::vector<std::vector<DiEdge>> Edges(MaxNumLanes);

  // Include unresolved vector uses
  for (unsigned i = 0; i < UnresolvedPacks.size(); i++) {
    const OperandPack &OP = *UnresolvedPacks[i];
    for (unsigned j = 0; j < OP.size(); j++) {
      Value *V = OP[j];
      auto *I = dyn_cast<Instruction>(V);
      // Skip `I` is frozen (and therefore resolved)
      if (!I || I->getParent() != BB || !Frt->isFree(I))
        continue;
      Edges[j].emplace_back(i, Index.getValueId(I));
    }
  }

  unsigned i = UnresolvedPacks.size();
  // Include unresolved scalar uses
  for (auto *V : Frt->getUnresolvedScalars()) {
    // Pretend scalar uses are degenerate vector use
    // and assign them to the first lane.
    Edges[0].emplace_back(i++, Index.getValueId(V));
  }

  unsigned NumUnresolvedUses = i;

  std::vector<torch::Tensor> Graphs;
  for (auto &E : Edges)
    Graphs.push_back(
        buildAdjacencyMat(E, NumUnresolvedUses, Index.getNumValues()));
  return Graphs;
}

// uv means u is *used by* v
static torch::Tensor buildInverseUnresolvedUseGraph(const Frontier *Frt,
                                                    Packer *Pkr,
                                                    IRIndex &Index) {
  BasicBlock *BB = Frt->getBasicBlock();
  auto UnresolvedPacks = Frt->getUnresolvedPacks();
  std::vector<DiEdge> Edges;
  // Include unresolved vector uses
  for (unsigned i = 0; i < UnresolvedPacks.size(); i++) {
    const OperandPack &OP = *UnresolvedPacks[i];
    for (unsigned j = 0; j < OP.size(); j++) {
      Value *V = OP[j];
      auto *I = dyn_cast<Instruction>(V);
      // Skip `I` is frozen (and therefore resolved)
      if (!I || I->getParent() != BB || !Frt->isFree(I))
        continue;
      Edges.emplace_back(Index.getValueId(I), i);
    }
  }

  unsigned i = UnresolvedPacks.size();
  // Include unresolved scalar uses
  for (auto *V : Frt->getUnresolvedScalars()) {
    // Pretend scalar uses are degenerate vector use
    // and assign them to the first lane.
    Edges.emplace_back(Index.getValueId(V), i++);
  }

  unsigned NumUnresolvedUses = i;
  return buildAdjacencyMat(Edges, Index.getNumValues(), NumUnresolvedUses);
}

PackDistribution PackingModelImpl::forward(const Frontier *Frt, Packer *Pkr,
                                           torch::Device Device,
                                           unsigned NumIters) {
  IRIndex Index(Frt);
  BasicBlock *BB = Frt->getBasicBlock();
  auto &LoadDAG = Pkr->getLoadDAG(BB);
  auto &StoreDAG = Pkr->getStoreDAG(BB);

  auto UseGraph1 = buildUseGraph1(Index).to(Device);
  auto UseGraph2 = buildUseGraph2(Index).to(Device);
  auto LeftMemRefGraph =
      buildLeftMemRefGraph(Index, LoadDAG, StoreDAG).to(Device);
  auto RightMemRefGraph =
      buildRightMemRefGraph(Index, LoadDAG, StoreDAG).to(Device);
  auto IndependenceGraph = buildIndependenceGraph(Frt, Pkr, Index).to(Device);

  auto InvUnresolvedGraph = buildInverseUnresolvedUseGraph(Frt, Pkr, Index);
  std::vector<torch::Tensor> UnresolvedUseGraphs =
      buildUnresolvedUseGraphs(Frt, Pkr, Index, MaxNumLanes);
  for (auto &G : UnresolvedUseGraphs)
    G = G.to(Device);


  unsigned N = Index.getNumValues();
  unsigned NumUnresolvedUses =
      Frt->getUnresolvedPacks().size() + Frt->numUnresolvedScalars();

  auto ValueTypes = getValueTypes(Index).to(Device);

  // Pass message from values to unresolved uses
  auto SendToUses = [&](torch::Tensor H_value) -> torch::Tensor {
    std::vector<torch::Tensor> Messages;
    for (auto &G : UnresolvedUseGraphs)
      Messages.push_back(torch::mm(G, H_value));
    return torch::cat(Messages, 1 /*dim*/);
  };

  // Pass message from values and unresolved uses to values themselves
  auto SendToValues = [&](torch::Tensor H_value,
                          torch::Tensor H_use) -> torch::Tensor {
    auto Msg1 = torch::mm(UseGraph1, StateToUseMsg1->forward(H_value));
    auto Msg2 = torch::mm(UseGraph2, StateToUseMsg2->forward(H_value));
    auto MemMsg = StateToMemMsg->forward(H_value);
    auto LeftMemMsg = torch::mm(LeftMemRefGraph, MemMsg);
    auto RightMemMsg = torch::mm(RightMemRefGraph, MemMsg);
    auto Independent =
        torch::mm(IndependenceGraph, StateToIndependentMsg(H_value));
    auto Unresolved = torch::mm(InvUnresolvedGraph, UnresolvedToMsg->forward(H_use));
    return torch::cat(
        {Msg1, Msg2, LeftMemMsg, RightMemMsg, Independent, Unresolved},
        1 /*dim*/);
  };

  // Initialize the states
  auto H_value = OpcodeEmb->forward(ValueTypes).view({N, EmbSize});
  auto H_use = InitUse.repeat({NumUnresolvedUses, 1});

  for (unsigned i = 0; i < NumIters; i++) {
    H_use = UseGRU->forward(SendToUses(H_value), H_use);
    H_value = ValueGRU->forward(SendToValues(H_value, H_use), H_value);
  }

  PackDistribution PD;

  PD.OpProb = StateToOpcode->forward(H_value);

  auto Emb = StateToEmb->forward(H_value);
  for (auto &StateToLaneEmb : StateToLaneEmbs) {
    PD.LaneProbs.push_back(
        StateToLaneEmb->forward(H_value).mm(Emb.t()).softmax(1 /*dim*/));
  }

  return PD;
}
