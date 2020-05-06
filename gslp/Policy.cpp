#include "Policy.h"

using namespace llvm;

static unsigned getInstId(PackingModel Model, const VectorPack *VP) {
  if (VP->isLoad() || VP->isStore())
    return Model->getMemAccessId(VP->getOrderedValues().size());
  auto *Inst = VP->getProducer();
  auto InstPool = Model->getInstPool();
  auto It = std::lower_bound(InstPool.begin(), InstPool.end(), Inst);
  assert(*It == Inst);
  return It - InstPool.begin();
}

torch::Tensor NeuralPackingPolicy::predict(
    const Frontier *Frt, llvm::ArrayRef<UCTNode::Transition> Transitions,
    Packer *Pkr) {
  PackDistribution PD = Model->forward(Frt, Pkr, Device, NumIters);

  std::vector<torch::Tensor> Prob;
  auto *Focus = Frt->getNextFreeInst();
  assert(Focus);
  unsigned FocusId = PD.Index.getValueId(Focus);
  for (const auto &T : Transitions) {
    if (!T.VP) {
      // Scalar (i.e., nop).
      Prob.push_back(PD.OpProb[FocusId][Model->getNopId()]);
      continue;
    }
    // T involves an actual pack.
    // We pretend we can sample the opcode and lanes independently
    auto PackProb = PD.OpProb[FocusId][getInstId(Model, T.VP)];
    unsigned i = 0;
    for (auto *V : T.VP->getOrderedValues())
      PackProb *= PD.LaneProbs[i++][FocusId][PD.Index.getValueId(V)];
    Prob.push_back(PackProb);
  }
  auto Predicted = torch::stack(Prob);
  return Predicted / Predicted.sum();
}

void NeuralPackingPolicy::predict(const Frontier *Frt,
               llvm::ArrayRef<UCTNode::Transition> Transitions, Packer *Pkr,
               std::vector<float> &Prob) {
  auto Predicted = predict(Frt, Transitions, Pkr).to(torch::Device(torch::kCPU));
  Prob = llvm::ArrayRef<float>(Predicted.data_ptr<float>(), Predicted.size(0)).vec();
}
