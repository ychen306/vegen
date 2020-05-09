#ifndef IR_MODEL_H
#define IR_MODEL_H

#include "LocalDependenceAnalysis.h"
#include "Preprocessing.h"
#include "Util.h"
#include <llvm/ADT/DenseMap.h>
#include <torch/torch.h>

class InstBinding;

struct PackDistribution {
  IRIndex Index;
  torch::Tensor OpProb;
  std::vector<torch::Tensor> LaneProbs;
  PackDistribution(IRIndex &&Index) : Index(Index) {}
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
