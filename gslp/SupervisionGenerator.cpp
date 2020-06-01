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
  float TotalCost = 0;
  while (!Node->isTerminal()) {
    MCTS.run(Node, NumIters);
    assert(Node->expanded());

    auto &Transitions = Node->transitions();

    UCTNode::Transition *T;
    if (Transitions.size() == 1) {
      // Don't bother querying the policy if there's no decision to make.
      T = &*Transitions.begin();
    } else if (Policy) {
      // If there's a policy, just take the transition w/ the highest prob.
      ArrayRef<float> TransitionWeight = Node->transitionWeight();

      // In the unlikely event that we don't have the weights,
      // query the network directly.
      std::vector<float> Prob;
      if (TransitionWeight.empty()) {
        Policy->predict(Node, Prob);
        TransitionWeight = Prob;
      }

      assert(TransitionWeight.size() == Transitions.size());

      auto It = std::max_element(TransitionWeight.begin(), TransitionWeight.end());
      T = &Transitions[It - TransitionWeight.begin()];
    } else {
      // Without a policy, we just follow the transition visited the most
      T = &*std::max_element(Transitions.begin(), Transitions.end(),
                                 UCTNode::compareByVisitCount);
    }
    Nodes.push_back(Node);
    Node = T->Next;
    TotalCost += T->Cost;
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
