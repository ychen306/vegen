#ifndef POLICY_H
#define POLICY_H
#include "IRModel.h"
#include "Solver.h"
#include "llvm/Support/ThreadPool.h"

class Packer;

class NeuralPackingPolicy : public PackingPolicy {
  PackingModel Model;
  Packer *Pkr;
  unsigned NumIters;
  torch::Device Device;
  unsigned BatchSize;

  llvm::ThreadPool Threads;

  // Worklist of nodes we want to evaluate.
  std::vector<UCTNode *> Nodes;

public:
  NeuralPackingPolicy(PackingModel Model, Packer *Pkr, unsigned NumIters,
                      torch::Device Device, unsigned BatchSize = 128,
                      unsigned NumThreads = 1)
      : Model(Model), Pkr(Pkr), NumIters(NumIters), Device(Device),
        BatchSize(BatchSize), Threads(llvm::hardware_concurrency(NumThreads)) {
    Nodes.reserve(BatchSize);
  }
  void predictAsync(UCTNode *) override;
  void waitForInflight() override { Threads.wait(); }
};

#endif // end POLICY_H
