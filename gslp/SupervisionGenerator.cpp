#include "SupervisionGenerator.h"
#include "Util.h"

using namespace llvm;

void SupervisionGenerator::run(PackingPolicy *Policy, Packer *Pkr,
                               BasicBlock *BB) {
  UCTNodeFactory Factory;
  UCTSearch MCTS(C, W, &Factory, Pkr, Policy, Evaluator, Pkr->getTTI());

  UCTNode *Root =
      Factory.getNode(std::make_unique<Frontier>(BB, Pkr->getContext(BB)));

  UCTNode *Node = Root;
  std::vector<UCTNode *> Nodes = {Root};
  std::vector<float> Prob;
  while (!Node->isTerminal()) {
    MCTS.run(Node, NumIters);
    assert(Node->expanded());

    // The MCTS queries the policy (if there's one) asynchronously,
    // cancel all requests if they haven't been processed yet.
    if (Policy)
      Policy->cancel();

    auto &Transitions = Node->transitions();
    // Don't bother querying the policy if there's no decision to make.
    if (Transitions.size() == 1) {
      Node = Transitions.begin()->Next;
      continue;
    }

    if (Policy) {
      // If there's a policy, just take the transition w/ the highest prob.
      Policy->predict(Node, Prob);
      auto It = std::max_element(Prob.begin(), Prob.end());
      Node = Transitions[It - Prob.begin()].Next;
    } else {
      // Without a policy, we just follow the transition visited the most
      auto It = std::max_element(
          Transitions.begin(), Transitions.end(),
          [](const UCTNode::Transition &A, const UCTNode::Transition &B) {
            return A.visitCount() < B.visitCount();
          });
      Node = It->Next;
    }

    Nodes.push_back(Node);
  }

  // Sample `SamplesPerBlock` and dump the tree search result.
  std::random_shuffle(Nodes.begin(), Nodes.end(), rand_int);
  unsigned NumSamples = std::min<unsigned>(SamplesPerBlock, Nodes.size());
  for (unsigned i = 0; i < NumSamples; i++)
    writeTreeSearchPolicy(Writer, *Nodes[i], *Pkr, Model);
}
