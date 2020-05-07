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

torch::Tensor computeProb(PackingModel Model, const PackDistribution &PD,
                          const Frontier *Frt,
                          llvm::ArrayRef<UCTNode::Transition> Transitions) {
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

void NeuralPackingPolicy::predictAsync(UCTNode *Node) {
  Nodes.push_back(Node);
  if (Nodes.size() >= BatchSize) {
    // Is this javascript?
    Threads.async([Nodes = std::move(Nodes), &Model = Model, Device = Device,
                   Pkr = Pkr, NumIters = NumIters]() {
      // Run the batch of frontiers through the model
      std::vector<const Frontier *> Frontiers;
      Frontiers.reserve(Nodes.size());
      for (auto *Node : Nodes)
        Frontiers.push_back(Node->getFrontier());
      std::vector<PackDistribution> PDs =
          Model->batch_forward(Frontiers, Pkr, Device, NumIters);

      // Compute pack probability.
      torch::Device CPU(torch::kCPU);
      for (unsigned i = 0; i < Frontiers.size(); i++) {
        auto *Node = Nodes[i];
        auto Prob =
            computeProb(Model, PDs[i], Frontiers[i], Node->transitions());
        // This line is so beautify, I am crying :-).
        Node->updateTransitionWeight(new std::vector<float>(
            ArrayRef<float>(Prob.to(CPU).data_ptr<float>(), Prob.size(0))
                .vec()));
      }
    });
  }
}
