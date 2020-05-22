#include "Policy.h"
#include "ModelUtil.h"

using namespace llvm;

static llvm::ArrayRef<float> tensorToArrayRef(torch::Tensor X) {
  static torch::Device CPU(torch::kCPU);
  return llvm::ArrayRef<float>(X.to(CPU).template data_ptr<float>(), X.size(0));
}

torch::Tensor computeProb(PackingModel Model, const PackDistribution &PD,
                          const Frontier *Frt,
                          llvm::ArrayRef<UCTNode::Transition> Transitions) {
  std::vector<torch::Tensor> Prob;
  auto *Focus = Frt->getNextFreeInst();
  assert(Focus);
  unsigned FocusId = PD.index().getValueId(Focus);
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
        PackProb *= PD.LaneProbs[i++][FocusId][PD.index().getValueId(V)];
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
      QueueCond.wait(LockGuard,
                     [&] { return !Queue.empty() || Shutdown.load(); });

      if (Shutdown.load())
        break;

      Nodes = std::move(Queue.front());
      Queue.pop();
      NumInflights -= Nodes.size();
    }
    InflightCond.notify_all();

    {
      std::unique_lock<std::mutex> LockGuard(IdlingLock);
      --NumIdlingThreads;
    }

    // Run the batch of frontiers through the model
    std::vector<const Frontier *> Frontiers;
    Frontiers.reserve(Nodes.size());
    for (auto *Node : Nodes)
      Frontiers.push_back(Node->getFrontier());
    std::vector<PackDistribution> PDs =
        Model->batch_forward(Frontiers, Device, NumIters);

    BatchPackProbability BPP(Model->getMaxNumLanes(), Device);
    for (unsigned i = 0; i < Nodes.size(); i++) {
      auto *Node = Nodes[i];
      auto &PD = PDs[i];

      const IRIndex &Index = PD.Index.getValue();

      auto *Focus = Node->getFrontier()->getNextFreeInst();
      assert(Focus && "Can't evaluate terminal state");
      BPP.start(PD, Index.getValueId(Focus));
      for (auto &T : Node->transitions()) {
        std::vector<unsigned> Lanes;
        unsigned OpId;
        if (!T.VP) {
          OpId = Model->getNopId();
        } else {
          OpId = Model->getInstId(T.VP);
          for (auto *V : T.VP->getOrderedValues())
            Lanes.push_back(Index.getValueId(V));
        }
        BPP.addPack(OpId, Lanes);
      }
      BPP.finish();
    }

    std::vector<torch::Tensor> Predictions = BPP.get();

    torch::Device CPU(torch::kCPU);
    for (unsigned i = 0; i < Nodes.size(); i++)
      Nodes[i]->updateTransitionWeight(new std::vector<float>(
          tensorToArrayRef(Predictions[i].to(CPU)).vec()));

    {
      std::unique_lock<std::mutex> LockGuard(IdlingLock);
      ++NumIdlingThreads;
    }
    IdlingCond.notify_all();
  }
}

void NeuralPackingPolicy::predictAsync(UCTNode *Node) {
  Nodes.push_back(Node);
  int NumInflightsLocal = 0;
  if (Nodes.size() >= BatchSize) {
    {
      std::unique_lock<std::mutex> LockGuard(QueueLock);
      NumInflights += Nodes.size();
      Queue.push(std::move(Nodes));
      NumInflightsLocal = NumInflights;
    }
    QueueCond.notify_one();
  }
  if (MaxNumInflights != -1 && NumInflightsLocal > MaxNumInflights) {
    // Block until the number of inflight evaluation requests die down.
    std::unique_lock<std::mutex> LockGuard(QueueLock);
    InflightCond.wait(
        LockGuard, [&] { return NumInflights <= (unsigned)MaxNumInflights; });
  }
}

// Empty the task queue and wait for all inflight tasks to finish.
void NeuralPackingPolicy::cancel() {
  Nodes.clear();
  {
    std::unique_lock<std::mutex> LockGuard(QueueLock);
    Queue = decltype(Queue)();
  }
  std::unique_lock<std::mutex> LockGuard(IdlingLock);
  IdlingCond.wait(LockGuard,
                  [&] { return NumIdlingThreads == Threads.size(); });
}

void NeuralPackingPolicy::predict(UCTNode *Node,
                                  std::vector<float> &Predicted) {
  auto *Frt = Node->getFrontier();
  PackDistribution PD = Model->forward(Frt, Device, NumIters);
  auto Prob = computeProb(Model, PD, Frt, Node->transitions());
  Predicted = tensorToArrayRef(Prob).vec();
}

NeuralPackingPolicy::~NeuralPackingPolicy() {
  Shutdown.store(true);
  QueueCond.notify_all();
  for (auto &T : Threads)
    T.join();
}
