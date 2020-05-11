#ifndef MODEL_UTIL_H
#define MODEL_UTIL_H

#include "IRModel.h"
#include "llvm/ADT/ArrayRef.h"

// Given a bunch of vectors Xs (B x N) and a bunch of indices Is (B x M),
// return a flat tensor with shape `sum_i M_i`.
class BatchSelector {
  torch::Device Device;
  unsigned N;
  std::vector<torch::Tensor> Xs;
  std::vector<int64_t> I;

public:
  BatchSelector(torch::Device Device) : Device(Device), N(0) {
    Xs.push_back(torch::zeros({1}).to(Device));
  }
  void addBatch(torch::Tensor X, llvm::ArrayRef<int64_t> Indices);
  torch::Tensor get();
};

// Given batches of PackDistribution and
// a list of legal packs for each distribution,
// compute the normalized prob for those packs.
class BatchPackProbability {
  unsigned MaxNumLanes;
  BatchSelector BatchOpProb;
  std::vector<BatchSelector> BatchLaneProbs;
  // Number of legal packs for each distribution.
  std::vector<unsigned> NumPacks;

  // Per batch data.
  torch::Tensor OpProb;
  std::vector<torch::Tensor> LaneProbs;
  std::vector<int64_t> OpIds;
  std::vector<std::vector<int64_t>> PerLaneValueIds;

public:
  BatchPackProbability(unsigned MaxNumLanes, torch::Device Device);

  // Start a distribution
  void start(const PackDistribution &PD, unsigned FocusId);

  // finish current distribution
  void finish();

  // Specify a legal pack for the current distribution
  void addPack(unsigned OpId, llvm::ArrayRef<unsigned> Lanes);

  std::vector<torch::Tensor> get();
};

#endif // end MODEL_UTIL_H
