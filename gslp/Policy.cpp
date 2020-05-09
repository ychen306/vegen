#include "Policy.h"

using namespace llvm;

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
    } else {
      // T involves an actual pack.
      // We pretend we can sample the opcode and lanes independently
      auto PackProb = PD.OpProb[FocusId][Model->getInstId(T.VP)];
      unsigned i = 0;
      for (auto *V : T.VP->getOrderedValues())
        PackProb *= PD.LaneProbs[i++][FocusId][PD.Index.getValueId(V)];
      Prob.push_back(PackProb);
    }
  }
  auto Predicted = torch::stack(Prob);
  return Predicted / Predicted.sum();
}

void NeuralPackingPolicy::evalNodes() {
  std::vector<UCTNode *> Nodes;
  while (!Shutdown.load()) {
    // Grab a batch of nodes from the queue
    {
      std::unique_lock<std::mutex> LockGuard(QueueLock);
      QueueCond.wait(LockGuard, [&] { return !Queue.empty() || Shutdown.load(); });

      if (Shutdown.load())
        break;

      Nodes = std::move(Queue.front());
      Queue.pop();
    }

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
      auto Prob = computeProb(Model, PDs[i], Frontiers[i], Node->transitions());
      // This line is so beautify, I am crying :-).
      Node->updateTransitionWeight(new std::vector<float>(
          ArrayRef<float>(Prob.to(CPU).data_ptr<float>(), Prob.size(0)).vec()));
    }
  }
}

void NeuralPackingPolicy::predictAsync(UCTNode *Node) {
  Nodes.push_back(Node);
  if (Nodes.size() >= BatchSize) {
    {
      std::unique_lock<std::mutex> LockGuard(QueueLock);
      Queue.push(std::move(Nodes));
    }
    QueueCond.notify_one();
  }
}

NeuralPackingPolicy::~NeuralPackingPolicy() {
  Shutdown.store(true);
  QueueCond.notify_all();
  for (auto &T : Threads)
    T.join();
}
