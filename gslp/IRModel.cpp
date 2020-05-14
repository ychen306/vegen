#include "IRModel.h"
#include "GraphUtil.h"
#include "MatchManager.h"
#include "Packer.h"
#include "Preprocessing.h"
#include "Solver.h"
#include "llvm/Support/FormatVariadic.h"
#include <map>
#include <torch/nn/module.h>
#include <torch/torch.h>

using namespace llvm;
using namespace torch;

namespace {

template <typename OutStreamTy>
void dumpShape(torch::Tensor X, OutStreamTy &Os) {
  for (auto N : X.sizes()) {
    Os << " " << N;
  }
  Os << '\n';
}

torch::Tensor getValueTypesAsTensor(llvm::ArrayRef<IRIndex> Indexes) {
  std::vector<int64_t> ValueTypes = getValueTypes(Indexes);
  return torch::from_blob(ValueTypes.data(), {(int64_t)ValueTypes.size()},
                          torch::TensorOptions().dtype(torch::kInt64))
      .clone();
}

} // end anonymous namespace

unsigned PackingModelImpl::getInstId(const VectorPack *VP) const {
  if (VP->isLoad() || VP->isStore())
    return getMemAccessId(VP->getOrderedValues().size());
  auto *Inst = VP->getProducer();
  auto It = std::lower_bound(InstPool.begin(), InstPool.end(), Inst);
  assert(*It == Inst);
  return It - InstPool.begin();
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

std::vector<PackDistribution> PackingModelImpl::batch_forward(
    const BatchedFrontier &Frt, torch::Device Device,
    llvm::Optional<std::vector<IRIndex>> Indexes, unsigned NumIters) {
  auto ValueTypes = Frt.ValueTypes.to(Device);
  auto UseGraph1 = Frt.Use1.to(Device);
  auto UseGraph2 = Frt.Use2.to(Device);
  auto LeftMemRefGraph = Frt.LeftMemRef.to(Device);
  auto RightMemRefGraph = Frt.RightMemRef.to(Device);
  auto IndependenceGraph = Frt.Independence.to(Device);
  auto InvUnresolvedGraph = Frt.InvUnresolved.to(Device);
  std::vector<torch::Tensor> UnresolvedUseGraphs;
  for (auto &U : Frt.Unresolved)
    UnresolvedUseGraphs.push_back(U.to(Device));

  // Initialize the states
  auto H_value =
      OpcodeEmb->forward(ValueTypes).view({Frt.TotalValues, EmbSize});
  auto H_use = InitUse.repeat({Frt.TotalUses, 1});

  // Pass message from values to unresolved uses
  auto SendToUses = [&](torch::Tensor H_value) -> torch::Tensor {
    std::vector<torch::Tensor> Messages;
    for (auto &G : UnresolvedUseGraphs)
      Messages.push_back(torch::mm(G, H_value));
    return torch::cat(Messages, 1 /*dim*/);
  };

  auto Zeros = torch::zeros({Frt.TotalValues, EmbSize}).to(Device);

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
    auto Unresolved = Frt.TotalUses ? torch::mm(InvUnresolvedGraph,
                                                UnresolvedToMsg->forward(H_use))
                                    : Zeros;
    return torch::cat(
        {Msg1, Msg2, LeftMemMsg, RightMemMsg, Independent, Unresolved},
        1 /*dim*/);
  };

  for (unsigned i = 0; i < NumIters; i++) {
    if (Frt.TotalUses)
      H_use = UseGRU->forward(SendToUses(H_value), H_use);
    H_value = ValueGRU->forward(SendToValues(H_value, H_use), H_value);
  }

  // Read out the probs in batch
  auto OpProb = StateToOpcode->forward(H_value);
  std::vector<torch::Tensor> LaneProbs;
  auto Emb = StateToEmb->forward(H_value);

  // Unpack the probs
  std::vector<PackDistribution> PDs;
  unsigned Offset = 0;
  for (unsigned i = 0; i < Frt.size(); i++) {
    unsigned N = Frt.NumValues[i];
    auto Slice = [Offset, N](torch::Tensor X) -> torch::Tensor {
      return X.slice(0 /*dim*/, Offset, Offset + N);
    };
    PackDistribution PD;
    if (Indexes)
      PD = PackDistribution(std::move(Indexes.getValue()[i]));
    PD.OpProb = Slice(OpProb).log_softmax(1/*dim*/);
    for (auto &StateToLaneEmb : StateToLaneEmbs)
      PD.LaneProbs.push_back(StateToLaneEmb->forward(Slice(H_value))
                                 .mm(Slice(Emb).t())
                                 .log_softmax(1 /*dim*/));
    Offset += N;
    PDs.push_back(std::move(PD));
  }
  return PDs;
}

std::vector<PackDistribution>
PackingModelImpl::batch_forward(llvm::ArrayRef<const Frontier *> Frontiers,
                                Packer *Pkr, torch::Device Device,
                                unsigned NumIters) {
  std::vector<IRIndex> Indexes;
  FrontierPreprocessor<BatchedGraphBuilder> Preprocessor(MaxNumLanes);

  BatchedFrontier Batched;

  for (auto *Frt : Frontiers) {
    IRIndex Index(Frt);
    unsigned NumValues;
    unsigned NumUses;
    // Build up the various graphs representing a frontier.
    Preprocessor.process(Frt, Index, Pkr, NumValues, NumUses);

    Indexes.push_back(std::move(Index));

    Batched.TotalValues += NumValues;
    Batched.TotalUses += NumUses;
    Batched.NumValues.push_back(NumValues);
    Batched.NumUses.push_back(NumUses);
  }

  Batched.Use1 = Preprocessor.use1().getBatched();
  Batched.Use2 = Preprocessor.use2().getBatched();
  Batched.LeftMemRef = Preprocessor.memRefs().getBatched();
  Batched.RightMemRef = Preprocessor.memRefs().getBatched(true /*flip*/);
  Batched.Independence = Preprocessor.independence().getBatched();
  Batched.InvUnresolved = Preprocessor.invUnresolved().getBatched();
  for (auto &U : Preprocessor.unresolved())
    Batched.Unresolved.push_back(U.getBatched());

  Batched.ValueTypes = getValueTypesAsTensor(Indexes);

  return batch_forward(std::move(Batched), Device, std::move(Indexes),
                       NumIters);
}

PackDistribution PackingModelImpl::forward(const Frontier *Frt, Packer *Pkr,
                                           torch::Device Device,
                                           unsigned NumIters) {
  std::vector<PackDistribution> PDs = batch_forward(Frt, Pkr, Device, NumIters);
  return std::move(PDs[0]);
}
