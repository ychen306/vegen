#ifndef IR_MODEL_H
#define IR_MODEL_H

#include "Preprocessing.h"
#include "Util.h"
#include <torch/torch.h>
#include <llvm/ADT/DenseMap.h>

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

class Packer;
class PackingModelImpl : public torch::nn::Module {
  unsigned EmbSize;
  llvm::ArrayRef<InstBinding *> InstPool;
  unsigned MaxNumLanes;

  torch::nn::Embedding OpcodeEmb = nullptr;

  // Init state for unresolved uses (we want to learn this0
  torch::Tensor InitUse;

  // Messagees
  torch::nn::Linear StateToUseMsg1 = nullptr;
  torch::nn::Linear StateToUseMsg2 = nullptr;
  torch::nn::Linear StateToMemMsg = nullptr;
  torch::nn::Linear StateToIndependentMsg = nullptr;
  torch::nn::Linear StateToUnresolvedMsg = nullptr;

  torch::nn::Linear UnresolvedToMsg = nullptr;

  // Read out
  torch::nn::Linear StateToEmb = nullptr;
  torch::nn::Linear StateToOpcode = nullptr;
  std::vector<torch::nn::Linear> StateToLaneEmbs;

  // Used to combine messages and node embeddings
  torch::nn::GRUCell ValueGRU = nullptr;
  // Used to combine lanes of unresolved vector uses
  torch::nn::GRUCell UseGRU = nullptr;

public:
  PackingModelImpl(unsigned EmbSize, llvm::ArrayRef<InstBinding *> Insts,
                   unsigned MaxNumLanes = 8);
  std::vector<PackDistribution> batch_forward(llvm::ArrayRef<const Frontier *>,
                                              Packer *, torch::Device,
                                              unsigned NumIters);
  std::vector<PackDistribution>
  batch_forward(const BatchedFrontier &Frt, torch::Device Device,
                llvm::Optional<std::vector<IRIndex>> Indexes,
                unsigned NumIters);
  PackDistribution forward(const Frontier *, Packer *, torch::Device,
                           unsigned NumIters);
  // TODO: pull `getNopID`, `getMemAccessId`, and `getInstId`
  // into a separate class that deals with assigning instruction id.
  unsigned getNopId() const { return InstPool.size(); }
  unsigned getMemAccessId(unsigned VL) const {
    return InstPool.size() + VL - 2;
  }
  unsigned getInstId(const VectorPack *) const;
  unsigned getMaxNumLanes() const { return MaxNumLanes; }
};

TORCH_MODULE(PackingModel);

#endif // IR_MODEL_H
