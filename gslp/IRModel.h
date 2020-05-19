#ifndef IR_MODEL_H
#define IR_MODEL_H

#include "Preprocessing.h"
#include "Util.h"
#include <llvm/ADT/DenseMap.h>
#include <torch/torch.h>

class InstBinding;

struct PackDistribution {
  llvm::Optional<IRIndex> Index;
  torch::Tensor OpProb;
  std::vector<torch::Tensor> LaneProbs;
  PackDistribution(IRIndex &&Index) : Index(Index) {}
  PackDistribution() = default;

  const IRIndex &index() const { return Index.getValue(); }
};

struct BatchedFrontier {
  std::vector<unsigned> NumValues;
  std::vector<unsigned> NumUses;
  unsigned TotalValues;
  unsigned TotalUses;
  torch::Tensor Use1;
  torch::Tensor Use2;
  torch::Tensor LeftMemRef;
  torch::Tensor RightMemRef;
  torch::Tensor Independence;
  torch::Tensor InvUnresolved;
  std::vector<torch::Tensor> Unresolved;
  torch::Tensor ValueTypes;

  BatchedFrontier() : TotalValues(0), TotalUses(0) {}

  // Return the batch size
  unsigned size() const { return NumValues.size(); }
};

class MLPImpl : public torch::nn::Module {
  torch::nn::Sequential Layers;

public:
  MLPImpl(unsigned InSize, unsigned OutSize, unsigned HiddenSize,
          unsigned NumLayers = 2);
  torch::Tensor forward(torch::Tensor X) { return Layers->forward(X); }
};
TORCH_MODULE(MLP);

class PackingModelImpl : public torch::nn::Module {
  unsigned EmbSize;
  llvm::ArrayRef<InstBinding *> InstPool;
  unsigned MaxNumLanes;

  torch::nn::Embedding OpcodeEmb = nullptr;

  // Init state for unresolved uses (we want to learn this0
  torch::Tensor InitUse;

  // Messagees
  MLP StateToUseMsg1 = nullptr;
  MLP StateToUseMsg2 = nullptr;
  MLP StateToMemMsg = nullptr;
  MLP StateToIndependentMsg = nullptr;
  MLP StateToUnresolvedMsg = nullptr;

  MLP UnresolvedToMsg = nullptr;

  // Read out
  MLP StateToEmb = nullptr;
  MLP StateToOpcode = nullptr;
  std::vector<MLP> StateToLaneEmbs;

  // Used to combine messages and node embeddings
  torch::nn::LSTMCell ValueRNN = nullptr;
  // Used to combine lanes of unresolved vector uses
  torch::nn::LSTMCell UseRNN = nullptr;

public:
  PackingModelImpl(unsigned EmbSize, llvm::ArrayRef<InstBinding *> Insts,
                   unsigned MaxNumLanes = 8);
  std::vector<PackDistribution> batch_forward(llvm::ArrayRef<const Frontier *>,
                                              torch::Device, unsigned NumIters);
  std::vector<PackDistribution>
  batch_forward(const BatchedFrontier &Frt, torch::Device Device,
                llvm::Optional<std::vector<IRIndex>> Indexes,
                unsigned NumIters);
  PackDistribution forward(const Frontier *, torch::Device, unsigned NumIters);
  // TODO: pull `getNopID`, `getMemAccessId`, and `getInstId`
  // into a separate class that deals with assigning instruction id.
  unsigned getNopId() const { return InstPool.size(); }
  unsigned getMemAccessId(unsigned VL) const {
    // A vectorized load/store has at least 2 lanes 
    return InstPool.size() + 1 + VL - 2;
  }
  unsigned getInstId(const VectorPack *) const;
  unsigned getMaxNumLanes() const { return MaxNumLanes; }
};

TORCH_MODULE(PackingModel);

#endif // IR_MODEL_H
