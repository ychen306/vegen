#include "IRModel.h"
#include "MatchManager.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
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
                                bool Flip = false) {
  auto CooIndices = torch::empty({2, (long long)Edges.size()},
                                 TensorOptions().dtype(torch::kInt64));
  for (unsigned i = 0; i < Edges.size(); i++) {
    if (Flip) {
      CooIndices[0][i] = (long long)Edges[i].Src;
      CooIndices[1][i] = (long long)Edges[i].Dest;
    } else {
      CooIndices[1][i] = (long long)Edges[i].Src;
      CooIndices[0][i] = (long long)Edges[i].Dest;
    }
  }
  return torch::sparse_coo_tensor(
      CooIndices, torch::ones({(long long)Edges.size()}), {N, N});
}

// Sample from a subset and return (re-normalized) log-prob of the sample
std::pair<unsigned, torch::Tensor>
sampleFromSubset(torch::Tensor Probs, std::vector<int64_t> &SubsetIndices) {
  auto Indices =
      torch::from_blob(SubsetIndices.data(), {(long long)SubsetIndices.size()},
                       TensorOptions().dtype(torch::kInt64)).clone();
  auto SubsetProbs = Probs.index_select(0, Indices);
  auto i = torch::multinomial(SubsetProbs, 1).item<int64_t>();
  // Need to renormalize the probability
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

IRIndex::IRIndex(llvm::Function &F) {
  auto ProcessValue = [&](Value *V) {
    if (Value2IdMap.count(V))
      return;
    unsigned Id = Values.size();
    Values.push_back(V);
    Value2IdMap[V] = Id;
  };

  for (auto &I : make_range(inst_begin(F), inst_end(F))) {
    ProcessValue(&I);
    for (Value *Operand : I.operands())
      ProcessValue(Operand);
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

static torch::Tensor getValueTypes(const IRIndex &Index) {
  unsigned N = Index.getNumValues();
  auto ValueTypes = torch::empty({N}, TensorOptions().dtype(torch::kInt64));
  for (unsigned i = 0; i < N; i++)
    ValueTypes[i] = (long long)OpTable.getValueTypeId(Index.get(i));
  return ValueTypes;
}

PackModelImpl::PackModelImpl(unsigned EmbSize, llvm::ArrayRef<InstBinding *> Insts)
    : EmbSize(EmbSize), Insts(Insts) {
  // lstm : <user> x <operand 1> x <operand 2> x <left mem refs> x <right mem refs> ->
  // (h, c)
  auto GRUOpt =
      nn::GRUOptions(EmbSize * 5, EmbSize).layers(1).batch_first(true);

  // # of possible pack opcode : <no pack> + <# of general packs> + store
  // TODO: support phi and load
  unsigned NumPackOps = Insts.size() + 1 + 1;

  GRU = register_module("lstm", nn::GRU(GRUOpt));
  OpcodeEmb = register_module(
      "opcode_embedding",
      nn::Embedding(nn::EmbeddingOptions(OpTable.getNumValueTypes(), EmbSize)));
  StateToUserMsg = register_module("state2user", nn::Linear(EmbSize, EmbSize));
  StateToUseMsg1 = register_module("state2msg1", nn::Linear(EmbSize, EmbSize));
  StateToUseMsg2 = register_module("state2msg2", nn::Linear(EmbSize, EmbSize));
  StateToMemMsg = register_module("state2mem", nn::Linear(EmbSize, EmbSize));
  StateToEmb = register_module("state2out", nn::Linear(EmbSize, EmbSize));
  StateToNop = register_module("state2nop", nn::Linear(EmbSize, EmbSize));
  StateToInst = register_module("state2inst", nn::Linear(EmbSize, NumPackOps));
}

PackDistribution PackModelImpl::forward(
    const IRIndex &Index,
    DenseMap<BasicBlock *, std::unique_ptr<ConsecutiveAccessDAG>> &LoadDAGs,
    DenseMap<BasicBlock *, std::unique_ptr<ConsecutiveAccessDAG>> &StoreDAGs,
    unsigned NumIters) {
  // FIXME: hoist these out
  auto InvUseGraph = buildInvUseGraph(Index);
  auto UseGraph1 = buildUseGraph1(Index);
  auto UseGraph2 = buildUseGraph2(Index);
  auto LeftMemRefGraph = buildLeftMemRefGraph(Index, LoadDAGs, StoreDAGs);
  auto RightMemRefGraph = buildRightMemRefGraph(Index, LoadDAGs, StoreDAGs);

  unsigned N = Index.getNumValues();

  // Initialize the states
  auto ValueTypes = getValueTypes(Index);
  auto H = OpcodeEmb->forward(ValueTypes).view({1, N, EmbSize});

  auto GetMessages = [&](torch::Tensor H) -> torch::Tensor {
    H = H.view({N, EmbSize});
    auto MemMsg = StateToMemMsg->forward(H);

    auto UserMsg = torch::mm(InvUseGraph, StateToUserMsg->forward(H));
    auto Msg1 = torch::mm(UseGraph1, StateToUseMsg1->forward(H));
    auto Msg2 = torch::mm(UseGraph2, StateToUseMsg2->forward(H));
    auto LeftMemMsg = torch::mm(LeftMemRefGraph, MemMsg);
    auto RightMemMsg = torch::mm(RightMemRefGraph, MemMsg);

    return torch::cat({UserMsg, Msg1, Msg2, LeftMemMsg, RightMemMsg}, 1 /*dim*/);
  };

  for (unsigned i = 0; i < NumIters; i++) {
    auto Msg = GetMessages(H);
    H = GRU->forward(Msg.view({N, 1, -1}), H).state;
  }

  H = H.view({N, EmbSize});
  // std::cerr << H << '\n';

  auto OpProb = StateToInst->forward(H).softmax(1 /*dim*/);
  auto Emb = StateToEmb->forward(H);
  auto Nop = StateToNop->forward(H);
  return PackDistribution(OpProb, Emb, Nop);
}

static const unsigned OpcodeNoPack = 0;
static const unsigned OpcodeStore = 1;

static const unsigned MaxNumLoads = 8;

// Check if `I` is checkIndependence from things in `Elements`, which depends on
// `Depended`.
static bool checkIndependence(const LocalDependenceAnalysis &LDA,
                              const VectorPackContext &VPCtx, Instruction *I,
                              const BitVector &Elements,
                              const BitVector &Depended) {
  auto Depended2 = LDA.getDepended(I);
  unsigned Id = VPCtx.getScalarId(I);
  return !Elements.test(Id) && !Elements.anyCommon(Depended2) &&
         !Depended.test(Id);
}

PackSample PackDistribution::sample(
    const IRIndex &Index, Instruction *Focus,
    const VectorPackSet &ExistingPacks, llvm::ArrayRef<InstBinding *> Insts,
    DenseMap<BasicBlock *, std::unique_ptr<LocalDependenceAnalysis>> &LDAs,
    DenseMap<BasicBlock *, std::unique_ptr<ConsecutiveAccessDAG>> &LoadDAGs,
    DenseMap<BasicBlock *, std::unique_ptr<ConsecutiveAccessDAG>> &StoreDAGs,
    DenseMap<BasicBlock *, std::unique_ptr<VectorPackContext>> &VPCtxs,
    DenseMap<BasicBlock *, std::unique_ptr<MatchManager>> &MMs,
    TargetTransformInfo *TTI) const {

  unsigned FocusId = Index.getValueId(Focus);

  auto NopEmb = Nop[FocusId];
  auto InstEmb = Emb[FocusId];
  auto Similarity = torch::cat({
      Emb.mv(InstEmb),
      NopEmb.dot(InstEmb).view({1})
      });
  auto InstProb = Similarity.softmax(0 /*dim*/);
  const unsigned NopId = Index.getNumValues();

  if (auto *SI = dyn_cast<StoreInst>(Focus)) {
    // Can't figure out how to convert a `0` literal to tensor...
    torch::Tensor Zero = torch::zeros({1}).sum();

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
    for (unsigned i = 0; i < MaxNumLoads; i++) {
      // Find the next set of adjacent
      auto It = StoreDAG.find(SI);
      if (It == StoreDAG.end())
        break;
      auto &Next = It->second;
      AvailableStores = {NopId};
      for (auto *SI2 : Next) {
        if (!checkIndependence(LDA, VPCtx, SI2, Elements, Depended))
          continue;
        if (ExistingPacks.isPacked(SI2, VPCtx))
          continue;
        AvailableStores.push_back(Index.getValueId(SI2));
      }
      torch::Tensor LaneLogProb;
      unsigned InstId;
      std::tie(InstId, LaneLogProb) =
          sampleFromSubset(InstProb, AvailableStores);
      if (InstId == NopId)
        break;
      VPLogProb += LaneLogProb;
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
      if (ExistingPacks.isPacked(I, VPCtx))
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
    std::tie(InstId, LaneLogProb) = sampleFromSubset(InstProb, MatchOutputs);
    VPLogProb += LaneLogProb;
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
