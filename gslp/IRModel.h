#ifndef IR_MODEL_H
#define IR_MODEL_H

#include "Util.h"
#include "LocalDependenceAnalysis.h"
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
  torch::Tensor LogProb;
};

// FIXME: PLEASE wrap these classes together
class VectorPackContext;
class VectorPackSet;
class LocalDependenceAnalysis;
class MatchManager;

struct PackDistribution {
  torch::Tensor OpProb;
  torch::Tensor InstProbs;
  PackDistribution(torch::Tensor OpProb, torch::Tensor InstProbs) 
    : OpProb(OpProb), InstProbs(InstProbs) {}
  PackSample sample(
      const IRIndex &Index,
      llvm::Instruction *Focus,
      const VectorPackSet &ExistingPacks,
      llvm::ArrayRef<InstBinding *> Insts,
      llvm::DenseMap<llvm::BasicBlock *, std::unique_ptr<LocalDependenceAnalysis>> &LDAs,
      llvm::DenseMap<llvm::BasicBlock *, std::unique_ptr<ConsecutiveAccessDAG>>
          &LoadDAG,
      llvm::DenseMap<llvm::BasicBlock *, std::unique_ptr<ConsecutiveAccessDAG>>
          &StoreDAG,
      llvm::DenseMap<llvm::BasicBlock *, std::unique_ptr<VectorPackContext>> &VPCtxs,
      llvm::DenseMap<llvm::BasicBlock *, std::unique_ptr<MatchManager>> &MMs,
      llvm::TargetTransformInfo *TTI) const;
};

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

public:
  PackModelImpl(unsigned EmbSize, llvm::ArrayRef<InstBinding *> Insts);
  PackDistribution forward(
      const IRIndex &Index,
      llvm::DenseMap<llvm::BasicBlock *, std::unique_ptr<ConsecutiveAccessDAG>>
          &LoadDAG,
      llvm::DenseMap<llvm::BasicBlock *, std::unique_ptr<ConsecutiveAccessDAG>>
          &StoreDAG,
      unsigned NumIters = 8);
};

TORCH_MODULE(PackModel);

#endif // IR_MODEL_H
