#include "SupervisionGenerator.h"
#include "Util.h"
#include "VectorPackSet.h"

using namespace llvm;

void SupervisionGenerator::run(PackingPolicy *Policy, PackingPolicy *NewPolicy,
                               Packer *Pkr, BasicBlock *BB) {
  UCTNodeFactory Factory;
  UCTSearch MCTS(C, W, EnumCap, ExpandThreshold, &Factory, Pkr, Policy,
                 Evaluator, Pkr->getTTI());

  UCTNode *Root = Factory.getNode(std::make_unique<Frontier>(BB, Pkr));

  StoreInst *S12 = nullptr;
  StoreInst *S13 = nullptr;

  StoreInst *S42 = nullptr;
  StoreInst *S43 = nullptr;

  Instruction *V90 = nullptr;
  Instruction *V91 = nullptr;

  Instruction *V100 = nullptr;
  Instruction *V101 = nullptr;

  Instruction *t4 = nullptr;

  for (auto &I : *BB) {
    if (auto *SI = dyn_cast<StoreInst>(&I)) {
      if (SI->getValueOperand()->getName() == "sub34")
        S43 = SI;
      if (SI->getValueOperand()->getName() == "sub30")
        S42 = SI;
      if (SI->getValueOperand()->getName() == "sub13")
        S12 = SI;
      if (SI->getValueOperand()->getName() == "sub16")
        S13 = SI;
    }
    if (I.getName() == "sub19")
      V90 = &I;
    if (I.getName() == "sub23")
      V91 = &I;
    if (I.getName() == "mul11")
      V100 = &I;
    if (I.getName() == "mul14")
      V101 = &I;
    if (I.getName() == "mul5")
      t4 = &I;
  }
  assert(S12 && S13 && S42 && S43 && V90 && V91 && V100 && V101 && t4);
  auto &MM = Pkr->getMatchManager(BB);
  auto *VPCtx = Pkr->getContext(BB);
  VectorPack *VP9, *VP10;
  auto &LDA = Pkr->getLDA(BB);
  auto *TTI = Pkr->getTTI();
  for (auto *Inst : Pkr->getInsts()) {
    auto LaneOps = Inst->getLaneOps();
    if (LaneOps.size() != 2)
      continue;

    auto *Op = LaneOps[0].getOperation();
    auto Matches = MM.getMatchesForOutput(Op, V90);
    if (!Matches.empty()) {
      // Inst should be the 2-lane vector fsub
      std::vector<const Operation::Match *> V9Lanes{
          &MM.getMatchesForOutput(Op, V90)[0],
          &MM.getMatchesForOutput(Op, V91)[0]};

      BitVector V9Elems(VPCtx->getNumValues());
      BitVector V9Depended(VPCtx->getNumValues());
      V9Elems.set(VPCtx->getScalarId(V90));
      V9Elems.set(VPCtx->getScalarId(V91));
      V9Depended |= LDA.getDepended(V90);
      V9Depended |= LDA.getDepended(V91);
      VP9 = VPCtx->createVectorPack(V9Lanes, V9Elems, V9Depended, Inst, TTI);
    }

    Matches = MM.getMatchesForOutput(Op, V100);
    if (!Matches.empty()) {
      // Inst should be the 2-lane vector fmul
      std::vector<const Operation::Match *> V10Lanes{
          &MM.getMatchesForOutput(Op, V100)[0],
          &MM.getMatchesForOutput(Op, V101)[0]};
      BitVector V10Elems(VPCtx->getNumValues());
      BitVector V10Depended(VPCtx->getNumValues());

      V10Elems.set(VPCtx->getScalarId(V100));
      V10Elems.set(VPCtx->getScalarId(V101));
      V10Depended |= LDA.getDepended(V100);
      V10Depended |= LDA.getDepended(V101);

      VP10 =
          VPCtx->createVectorPack(V10Lanes, V10Elems, V10Depended, Inst, TTI);
    }
  }

  BitVector VS1Elems(VPCtx->getNumValues());
  BitVector VS1Depended(VPCtx->getNumValues());
  BitVector VS4Elems(VPCtx->getNumValues());
  BitVector VS4Depended(VPCtx->getNumValues());
  std::vector<StoreInst *> VS1_Lanes{S12, S13};
  std::vector<StoreInst *> VS4_Lanes{S42, S43};
  VS1Elems.set(VPCtx->getScalarId(S12));
  VS1Elems.set(VPCtx->getScalarId(S13));
  VS4Elems.set(VPCtx->getScalarId(S42));
  VS4Elems.set(VPCtx->getScalarId(S43));

  VS1Depended |= LDA.getDepended(S12);
  VS1Depended |= LDA.getDepended(S13);
  VS4Depended |= LDA.getDepended(S42);
  VS4Depended |= LDA.getDepended(S43);

  auto *VS1 = VPCtx->createStorePack(VS1_Lanes, VS1Elems, VS1Depended, TTI);
  auto *VS4 = VPCtx->createStorePack(VS4_Lanes, VS4Elems, VS4Depended, TTI);

  UCTNode *Node = Root;
  std::vector<UCTNode *> Nodes;

  VectorPackSet Packs(BB->getParent());

  float TotalCost = 0;

  auto Frt = std::make_unique<Frontier>(BB, Pkr);
  TotalCost += Frt->advanceInplace(VS1, TTI);
  TotalCost += Frt->advanceInplace(VS4, TTI);
  for (auto &I : *BB) {
    if (auto *SI = dyn_cast<StoreInst>(&I)) {
      if (SI->getValueOperand() == t4)
        TotalCost += Frt->advanceInplace(SI, TTI);
    }
  }
  TotalCost += Frt->advanceInplace(t4, TTI);

  for (User *V : V90->users()) {
    auto *I = dyn_cast<Instruction>(V);
    if (I)
      TotalCost += Frt->advanceInplace(I, TTI);
  }
  for (User *V : V91->users()) {
    auto *I = dyn_cast<Instruction>(V);
    if (I)
      TotalCost += Frt->advanceInplace(I, TTI);
  }
  for (User *V : V100->users()) {
    auto *I = dyn_cast<Instruction>(V);
    if (I)
      TotalCost += Frt->advanceInplace(I, TTI);
  }
  for (User *V : V101->users()) {
    auto *I = dyn_cast<Instruction>(V);
    if (I)
      TotalCost += Frt->advanceInplace(I, TTI);
  }

  TotalCost += Frt->advanceInplace(VP9, TTI);
  TotalCost += Frt->advanceInplace(VP10, TTI);

  PackEnumerationCache EnumCache;
  errs() << "Init cost: "
         << TotalCost +
                Evaluator->evaluate(0, 0, Frt.get(), nullptr, EnumCache, Pkr)
         << '\n';

  outs() << BB->getModule()->getName() << '/' << BB->getParent()->getName()
         << '/' << BB->getName() << ' ';
  TotalCost = 0;
  //Node = Factory.getNode(std::move(Frt));

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
      // T = &*std::max_element(Transitions.begin(), Transitions.end(),

      //    //[](const UCTNode::Transition &A, const UCTNode::Transition &B) {
      //    //  return A.Cost + A.Next->minCost() > B.Cost + B.Next->minCost();
      //    //}

      //                           UCTNode::compareByVisitCount
      //                           );
      T = &*std::max_element(
          Transitions.begin(), Transitions.end(),

          [](const UCTNode::Transition &A, const UCTNode::Transition &B) {
              float ACost = -A.Cost - A.Next->minCost();
              float BCost = -B.Cost - B.Next->minCost();
            return std::tie(ACost, A.Count) < std::tie(BCost, B.Count);
          }
          );
    }
#if 1
    errs() << "====================================="
           << "\n\t t transition cost: " << T->transitionCost()
           << "\n\t num transitions: " << Transitions.size()
           << "\n\t scalar cost: " << Transitions.begin()->avgCost()
           << "\n\t t avg cost: " << T->avgCost()
           << "\n\t t->next avg cost: " << T->Next->avgCost()
           << "\n\t t->next min cost: " << T->Next->minCost()
           << "\n\t t->next terminal? " << T->Next->isTerminal()
           << "\n\t t visit count : " << T->visitCount()
           << "\n\t node visit count: " << Node->visitCount()
           << "\n\t min cost : " << Node->minCost()
           << "\n\t max cost : " << Node->maxCost()
           << "\n\t avg cost : " << Node->avgCost()
           << "\n\t num unresolved packs : "
           << Node->getFrontier()->getUnresolvedPacks().size()
           << "\n\t num unresolved scalars : "
           << Node->getFrontier()->numUnresolvedScalars() << '\n';
    if (T->VP) {
      errs() << "ADDING PACK " << *T->VP << '\n';
      Packs.tryAdd(T->VP);
    } else if (T->I) {
      errs() << "Scalarizing " << *T->I << '\n';
    }
#endif

    unsigned NumPacks = 0;
    for (auto &T : Transitions)
      if (T.VP || T.Next->getPartialPack() || Node->getPartialPack())
        NumPacks++;
    outs() << NumPacks << '/' << Transitions.size() << ' ';
    errs() << NumPacks << '/' << Transitions.size() << ' ';
    Nodes.push_back(Node);
    Node = T->Next;
    errs() << "~~~ " << TotalCost << ", " << T->Cost << '\n';
    TotalCost += T->Cost;
  }
  outs() << '\n';

  errs() << "Cost of " << BB->getParent()->getName() << "/" << BB->getName()
         << ": " << TotalCost << ", cost according to vector pack set: "
         << Packs.getCostSaving(Pkr->getTTI(), Pkr->getBFI()) << "\n\n";

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
