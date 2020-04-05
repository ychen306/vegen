#ifndef IR_MODEL_H
#define IR_MODEL_H

#include "Util.h"
#include <llvm/ADT/DenseMap.h>
#include <torch/torch.h>

class InstBinding;

namespace llvm {
class Function;
class BasicBlock;
class Value;
} // namespace llvm

class IRIndex {
  llvm::DenseMap<llvm::Value *, unsigned> Value2IdMap;
  std::vector<llvm::Value *> Values;

public:
  IRIndex(llvm::Function &F);
  unsigned getValueId(llvm::Value *V) const { return Value2IdMap.lookup(V); }
  llvm::Value *get(unsigned i) const { return Values[i]; }
  unsigned getNumValues() const { return Values.size(); }
};


class VectorPack;
struct PackSample {
  VectorPack *VP;
  torch::Tensor Prob;
};

class VectorPackContext;
struct PackDistribution {
  torch::Tensor InstProb;
  torch::Tensor Emb;
  PackDistribution(torch::Tensor InstProb, torch::Tensor Emb) 
    : InstProb(InstProb), Emb(Emb) {}
  PackSample sample(llvm::DenseMap<llvm::BasicBlock *, std::unique_ptr<VectorPackContext>> &VPCtxs);
};

class PackModel : torch::nn::Module {
  unsigned EmbSize;
  llvm::ArrayRef<InstBinding *> Insts;

  torch::nn::GRU GRU = nullptr;
  torch::nn::Embedding OpcodeEmb = nullptr;
  torch::nn::Linear StateToUseMsg1 = nullptr;
  torch::nn::Linear StateToUseMsg2 = nullptr;
  torch::nn::Linear StateToMemMsg = nullptr;
  torch::nn::Linear StateToInst = nullptr;
  torch::nn::Linear StateToEmb = nullptr;

public:
  PackModel(unsigned EmbSize, llvm::ArrayRef<InstBinding *> Insts);
  PackDistribution forward(
      const IRIndex &Index,
      llvm::DenseMap<llvm::BasicBlock *, std::unique_ptr<ConsecutiveAccessDAG>>
          &LoadDAG,
      llvm::DenseMap<llvm::BasicBlock *, std::unique_ptr<ConsecutiveAccessDAG>>
          &StoreDAG,
      unsigned NumIters = 8);
};

#endif // IR_MODEL_H
