#include "IRModel.h"
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Instructions.h>
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

static torch::Tensor buildUseGraph1(const IRIndex &Index) {
  std::vector<DiEdge> Edges;
  unsigned N = Index.getNumValues();
  for (unsigned i = 0; i < N; i++) {
    auto *V = Index.get(i);
    auto *I = dyn_cast<Instruction>(V);
    if (!I)
      continue;
    Edges.emplace_back(Index.getValueId(I), Index.getValueId(I->getOperand(0)));
  }
  return buildAdjacencyMat(Edges, N);
}

static torch::Tensor buildUseGraph2(const IRIndex &Index) {
  std::vector<DiEdge> Edges;
  unsigned N = Index.getNumValues();
  for (unsigned i = 0; i < N; i++) {
    auto *V = Index.get(i);
    auto *I = dyn_cast<Instruction>(V);
    if (!I || isa<LoadInst>(I))
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

PackModel::PackModel(unsigned EmbSize, llvm::ArrayRef<InstBinding *> Insts) : EmbSize(EmbSize), Insts(Insts) {
  // lstm : <operand 1> x <operand 2> x <left mem refs> x <right mem refs> ->
  // (h, c)
  auto GRUOpt =
      nn::GRUOptions(EmbSize * 4, EmbSize).layers(1).batch_first(true);

  // # of possible pack opcode : <no pack> + <# of general packs> + store
  // TODO: support phi and load
  unsigned NumInsts = Insts.size() + 1 + 1;

  GRU = register_module("lstm", nn::GRU(GRUOpt));
  OpcodeEmb = register_module(
      "opcode_embedding",
      nn::Embedding(nn::EmbeddingOptions(OpTable.getNumValueTypes(), EmbSize)));
  StateToUseMsg1 = register_module("state2msg1", nn::Linear(EmbSize, EmbSize));
  StateToUseMsg2 = register_module("state2msg2", nn::Linear(EmbSize, EmbSize));
  StateToMemMsg = register_module("state2mem", nn::Linear(EmbSize, EmbSize));
  StateToEmb = register_module("state2out", nn::Linear(EmbSize, EmbSize));
  StateToInst = register_module("state2inst", nn::Linear(EmbSize, NumInsts));
}

PackDistribution PackModel::forward(
    const IRIndex &Index,
    DenseMap<BasicBlock *, std::unique_ptr<ConsecutiveAccessDAG>> &LoadDAGs,
    DenseMap<BasicBlock *, std::unique_ptr<ConsecutiveAccessDAG>> &StoreDAGs,
    unsigned NumIters) {
  // FIXME: hoist these out
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

    auto Msg1 = torch::mm(UseGraph1, StateToUseMsg1->forward(H));
    auto Msg2 = torch::mm(UseGraph2, StateToUseMsg2->forward(H));
    auto LeftMemMsg = torch::mm(LeftMemRefGraph, MemMsg);
    auto RightMemMsg = torch::mm(RightMemRefGraph, MemMsg);

    return torch::cat({Msg1, Msg2, LeftMemMsg, RightMemMsg}, 1 /*dim*/);
  };

  for (unsigned i = 0; i < NumIters; i++) {
    auto Msg = GetMessages(H);
    H = GRU->forward(Msg.view({N, 1, -1}), H).state;
  }

  H = H.view({N, EmbSize});
  // std::cerr << H << '\n';

  auto InstProb = StateToInst->forward(H).softmax(1 /*dim*/);
  auto Emb = StateToEmb->forward(H);
  return PackDistribution(InstProb, Emb);
}
