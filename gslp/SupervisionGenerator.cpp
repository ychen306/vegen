#include "SupervisionGenerator.h"
#include "VectorPackSet.h"
#include "Util.h"

using namespace llvm;

void SupervisionGenerator::run(PackingPolicy *Policy, PackingPolicy *NewPolicy,
                               Packer *Pkr, BasicBlock *BB) {
  UCTNodeFactory Factory;
  UCTSearch MCTS(C, W, EnumCap, ExpandThreshold, &Factory, Pkr, Policy,
                 Evaluator, Pkr->getTTI());

  UCTNode *Root = Factory.getNode(std::make_unique<Frontier>(BB, Pkr));

  UCTNode *Node = Root;
  std::vector<UCTNode *> Nodes;

  VectorPackSet Packs(BB->getParent());

  float TotalCost = 0;
  outs() << BB->getModule()->getName() 
    << '/' << BB->getParent()->getName()
    << '/' << BB->getName() << ' ';

  while (!Node->isTerminal()) {
    MCTS.run(Node, NumIters);
    assert(Node->expanded());

    auto &Transitions = Node->transitions();

    UCTNode::Transition *T;
    if (Transitions.size() == 1) {
      // Don't bother querying the policy if there's no decision to make.
      T = &*Transitions.begin();
    } else if (NewPolicy) {
      // In the unlikely event that we don't have the weights,
      // query the network directly.
      std::vector<float> Prob;
      NewPolicy->predict(Node, Prob);

      assert(Prob.size() == Transitions.size());

      auto It = std::max_element(Prob.begin(), Prob.end());
      T = &Transitions[It - Prob.begin()];
    } else {
      // Without a policy, we just follow the transition visited the most
      T = &*std::max_element(Transitions.begin(), Transitions.end(),

          //[](const UCTNode::Transition &A, const UCTNode::Transition &B) {
          //  return A.Cost + A.Next->minCost() > B.Cost + B.Next->minCost();
          //}

                                 UCTNode::compareByVisitCount
                                 );
    }
#if 1
    errs() << "====================================="
      << "\n\t t cost: " << T->transitionCost() 
      << "\n\t num transitions: " << Transitions.size()
      << "\n\t scalar cost: " << Transitions.begin()->avgCost() 
      << "\n\t t cost: " << T->avgCost()
      << "\n\t t->next cost: " << T->Next->avgCost()
      << "\n\t t->next terminal? " << T->Next->isTerminal()
      << "\n\t t visit count : " << T->visitCount()
      << "\n\t node visit count: " << Node->visitCount()
      << "\n\t min cost : " << Node->minCost()
      << "\n\t max cost : " << Node->maxCost()
      << "\n\t avg cost : " << Node->avgCost()
      << '\n';
    if (T->VP) {
      errs() << "ADDING PACK " << *T->VP << '\n';
      Packs.tryAdd(T->VP);
    }
#endif

    unsigned NumPacks = 0;
    for (auto &T : Transitions)
      if (T.VP || T.Next->getPartialPack() || Node->getPartialPack())
        NumPacks++;
    outs() << NumPacks << '/' << Transitions.size() << ' ';
    Nodes.push_back(Node);
    Node = T->Next;
    errs() << "~~~ " << TotalCost << ", " << T->Cost << '\n';
    TotalCost += T->Cost;

  }
  outs() << '\n';


  errs() << "Cost of " << BB->getParent()->getName() << "/" << BB->getName() << ": " << TotalCost
    << ", cost according to vector pack set: " << Packs.getCostSaving(Pkr->getTTI(), Pkr->getBFI()) 
    << '\n\n';

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
