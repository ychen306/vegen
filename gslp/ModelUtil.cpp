#include "ModelUtil.h"

void BatchSelector::addBatch(torch::Tensor X, llvm::ArrayRef<int64_t> Indices) {
  Xs.push_back(X);
  for (unsigned i = 0; i < Indices.size(); i++) {
    // We reserve the first entry of the final flat vector to be zero
    // If an index is -1 it means we want X[i] = 0 forall X
    if (Indices[i] == -1)
      I.push_back(0);
    else
      I.push_back(N + Indices[i] + 1);
  }
  N += X.size(0);
}

torch::Tensor BatchSelector::get() {
  auto IdxTensor = torch::from_blob(I.data(), {(int64_t)I.size()},
                                    torch::TensorOptions().dtype(torch::kInt64))
                       .clone();
  return torch::cat(Xs).index(IdxTensor).to(Device);
}

BatchPackProbability::BatchPackProbability(unsigned MaxNumLanes,
                                           torch::Device Device)
    : MaxNumLanes(MaxNumLanes), BatchOpProb(Device), LaneProbs(MaxNumLanes),
      PerLaneValueIds(MaxNumLanes) {
  for (unsigned i = 0; i < MaxNumLanes; i++)
    BatchLaneProbs.emplace_back(Device);
}

void BatchPackProbability::start(const PackDistribution &PD, unsigned FocusId) {
  OpIds.clear();
  for (auto &ValueIds : PerLaneValueIds)
    ValueIds.clear();
  OpProb = PD.OpProb[FocusId];
  for (unsigned i = 0; i < MaxNumLanes; i++)
    LaneProbs[i] = PD.LaneProbs[i][FocusId];
}

void BatchPackProbability::finish() {
  BatchOpProb.addBatch(OpProb, OpIds);
  for (unsigned i = 0; i < MaxNumLanes; i++)
    BatchLaneProbs[i].addBatch(LaneProbs[i], PerLaneValueIds[i]);
  NumPacks.push_back(OpIds.size());
}

void BatchPackProbability::addPack(unsigned OpId,
                                   llvm::ArrayRef<unsigned> Lanes) {
  OpIds.push_back(OpId);
  for (unsigned i = 0; i < MaxNumLanes; i++) {
    if (i < Lanes.size())
      PerLaneValueIds[i].push_back(Lanes[i]);
    else
      PerLaneValueIds[i].push_back(-1);
  }
}

std::vector<torch::Tensor> BatchPackProbability::get() {
  auto RawLogProb = BatchOpProb.get();
  for (auto &LP : BatchLaneProbs)
    RawLogProb = RawLogProb + LP.get();
  auto RawProb = RawLogProb.clamp(-1e8).exp();

  // Unpack the flatten probs and renormalize them.
  std::vector<torch::Tensor> Probs;
  unsigned Offset = 0;
  for (unsigned N : NumPacks) {
    auto Prob = RawProb.slice(0 /*dim*/, Offset, Offset + N) + 1e-8;
    Probs.push_back(Prob / Prob.sum());
    Offset += N;
  }
  return Probs;
}
