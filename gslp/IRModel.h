#ifndef IR_MODEL_H
#define IR_MODEL_H

#include "LocalDependenceAnalysis.h"
#include "Util.h"
#include "VectorPackContext.h"
#include "VectorPackSet.h"
#include <llvm/ADT/DenseMap.h>
#include <torch/torch.h>

class InstBinding;

namespace llvm {
class Function;
class BasicBlock;
class Instruction;
class Value;

class TargetTransformInfo;
} // namespace llvm

class Frontier;
class IRIndex {
  llvm::DenseMap<llvm::Value *, unsigned> Value2IdMap;
  std::vector<llvm::Value *> Values;

  void trackValue(llvm::Value *);

public:
  IRIndex(llvm::Function &F);
  IRIndex(const Frontier *Frt);
  unsigned getValueId(llvm::Value *V) const { return Value2IdMap.lookup(V); }
  llvm::Value *get(unsigned i) const { return Values[i]; }
  unsigned getNumValues() const { return Values.size(); }
};

class VectorPack;
struct PackSample {
  VectorPack *VP;
  torch::Tensor LogProb;
};

// FIXME: PLEASE wrap these classes together
class VectorPackContext;
class VectorPackSet;
class LocalDependenceAnalysis;
class MatchManager;

struct PackDistributionDeprecated {
  torch::Tensor OpProb;
  std::vector<torch::Tensor> LaneProbs;

  PackDistributionDeprecated(torch::Tensor OpProb,
                             std::vector<torch::Tensor> LaneProbs)
      : OpProb(OpProb), LaneProbs(LaneProbs) {}

  PackSample sample(
      const IRIndex &Index, llvm::Instruction *Focus,
      const VectorPackSet &ExistingPacks, llvm::ArrayRef<InstBinding *> Insts,
      llvm::DenseMap<llvm::BasicBlock *,
                     std::unique_ptr<LocalDependenceAnalysis>> &LDAs,
      llvm::DenseMap<llvm::BasicBlock *, std::unique_ptr<ConsecutiveAccessDAG>>
          &LoadDAG,
      llvm::DenseMap<llvm::BasicBlock *, std::unique_ptr<ConsecutiveAccessDAG>>
          &StoreDAG,
      llvm::DenseMap<llvm::BasicBlock *, std::unique_ptr<VectorPackContext>>
          &VPCtxs,
      llvm::DenseMap<llvm::BasicBlock *, std::unique_ptr<MatchManager>> &MMs,
      llvm::TargetTransformInfo *TTI) const;

  torch::Tensor entropy() const;
};

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
  PackDistribution forward(const Frontier *, Packer *, torch::Device,
                           unsigned NumIters);
  unsigned getNopId() const { return InstPool.size(); }
  unsigned getMemAccessId(unsigned VL) const {
    return InstPool.size() + VL - 2;
  }
  llvm::ArrayRef<InstBinding *> getInstPool() const { return InstPool; }
};

TORCH_MODULE(PackingModel);

class PackModelImpl : public torch::nn::Module {
  unsigned EmbSize;
  llvm::ArrayRef<InstBinding *> Insts;

  torch::nn::Embedding OpcodeEmb = nullptr;

  torch::nn::GRUCell GRU = nullptr;
  torch::nn::Linear StateToUserMsg = nullptr;
  torch::nn::Linear StateToUseMsg1 = nullptr;
  torch::nn::Linear StateToUseMsg2 = nullptr;
  torch::nn::Linear StateToMemMsg = nullptr;
  torch::nn::Linear StateToInst = nullptr;
  torch::nn::Linear StateToEmb = nullptr;
  torch::nn::Linear StateToNop = nullptr;
  std::vector<torch::nn::Linear> StateToLaneEmbs;

public:
  PackModelImpl(unsigned EmbSize, llvm::ArrayRef<InstBinding *> Insts,
                unsigned MaxNumLanes = 64);
  PackDistributionDeprecated forward(
      torch::Device &Device, const IRIndex &Index,
      llvm::DenseMap<llvm::BasicBlock *, std::unique_ptr<ConsecutiveAccessDAG>>
          &LoadDAG,
      llvm::DenseMap<llvm::BasicBlock *, std::unique_ptr<ConsecutiveAccessDAG>>
          &StoreDAG,
      unsigned NumIters = 8);
};

TORCH_MODULE(PackModel);

void loadModel(PackModel &PackModel, std::string ModelPath);

#endif // IR_MODEL_H
