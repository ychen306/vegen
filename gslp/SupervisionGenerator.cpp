#include "SupervisionGenerator.h"
#include "Util.h"

using namespace llvm;

void SupervisionGenerator::run(PackingPolicy *Policy, Packer *Pkr,
                               BasicBlock *BB) {
  UCTNodeFactory Factory;
  UCTSearch MCTS(C, W, EnumCap, ExpandThreshold, &Factory, Pkr, Policy,
                 Evaluator, Pkr->getTTI());

  UCTNode *Root = Factory.getNode(std::make_unique<Frontier>(BB, Pkr));

  UCTNode *Node = Root;
  std::vector<UCTNode *> Nodes;
  std::vector<float> Prob;
  while (!Node->isTerminal()) {
    MCTS.run(Node, NumIters);
    assert(Node->expanded());

    auto &Transitions = Node->transitions();
    // Don't bother querying the policy if there's no decision to make.
    if (Transitions.size() == 1) {
      Node = Transitions.begin()->Next;
      continue;
    }

    UCTNode *NextNode;
    if (Policy) {
      // If there's a policy, just take the transition w/ the highest prob.
      ArrayRef<float> TransitionWeight = Node->transitionWeight();

      // In the unlikely event that we don't have the weights,
      // query the network directly.
      if (TransitionWeight.empty()) {
        Policy->predict(Node, Prob);
        TransitionWeight = Prob;
      }

      auto It = std::max_element(Prob.begin(), Prob.end());
      NextNode = Transitions[It - Prob.begin()].Next;
    } else {
      // Without a policy, we just follow the transition visited the most
      auto It = std::max_element(Transitions.begin(), Transitions.end(),
                                 UCTNode::compareByVisitCount);
      NextNode = It->Next;
    }

    Nodes.push_back(Node);
    Node = NextNode;
  }

  // The MCTS queries the policy (if there's one) asynchronously,
  // cancel all requests if they haven't been processed yet.
  if (Policy)
    Policy->cancel();

  // Sample `SamplesPerBlock` and dump the tree search result.
  std::random_shuffle(Nodes.begin(), Nodes.end(), rand_int);
  unsigned NumSamples = std::min<unsigned>(SamplesPerBlock, Nodes.size());
  for (unsigned i = 0; i < NumSamples; i++)
    writeTreeSearchPolicy(Archiver, *Nodes[i], *Pkr, Model);
}
