#ifndef POLICY_H
#define POLICY_H
#include "IRModel.h"
#include "Solver.h"

class NeuralPackingPolicy : public PackingPolicy {
  PackingModel Model;
  unsigned NumIters;
  torch::Device Device;

public:
  NeuralPackingPolicy(PackingModel Model, unsigned NumIters,
                      torch::Device Device)
      : Model(Model), NumIters(NumIters), Device(Device) {}
  void predict(const Frontier *Frt,
               llvm::ArrayRef<UCTNode::Transition> Transitions, Packer *Pkr,
               std::vector<float> &Prob) override;
  torch::Tensor predict(const Frontier *Frt,
                        llvm::ArrayRef<UCTNode::Transition> Transitions,
                        Packer *Pkr);
};

#endif // end POLICY_H
