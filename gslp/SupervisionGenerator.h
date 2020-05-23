#ifndef SUPERVISION_GENERATOR_H
#define SUPERVISION_GENERATOR_H

#include "IRModel.h"
#include "Serialize.h"
#include "Solver.h"

namespace llvm {
class BasicBlock;
}

//
// Run a MCTS (optionally parametrized by a policy),
// over data points and dumps out a few sampled nodes and
// their corresponding final tree policy.
//
class SupervisionGenerator {
  PolicyArchiver &Archiver;
  FrontierEvaluator *Evaluator;
  // FIXME: we are only using a model here to assign integer IDs to opcodes,
  // remove this after we refactor PackingModel
  PackingModel Model;
  unsigned EnumCap;
  unsigned ExpandThreshold;
  unsigned SamplesPerBlock;
  float C;
  float W;
  // Number of iterations we run MCTS
  unsigned NumIters;

public:
  SupervisionGenerator(PolicyArchiver &Archiver, FrontierEvaluator *Evaluator,
                       PackingModel Model, unsigned EnumCap, unsigned ExpandThreshold,
                       unsigned SamplesPerBlock, float C, float W,
                       unsigned NumIters = 1000)
      : Archiver(Archiver), Evaluator(Evaluator), Model(Model),
        EnumCap(EnumCap), ExpandThreshold(ExpandThreshold),
        SamplesPerBlock(SamplesPerBlock), C(C),
        W(W), NumIters(NumIters) {}
  // Run a policy-augmented MCTS on a basic block to generate supervision data
  void run(PackingPolicy *, Packer *, llvm::BasicBlock *);
};

#endif // end SUPERVISION_GENERATOR_H
