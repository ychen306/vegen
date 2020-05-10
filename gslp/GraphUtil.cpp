#include "GraphUtil.h"
#include "llvm/ADT/ArrayRef.h"

torch::Tensor buildAdjacencyMat(llvm::ArrayRef<DiEdge> Edges, unsigned N,
                                unsigned M, bool Flip = false) {
  auto Int64Ty = torch::TensorOptions().dtype(torch::kInt64);
  auto CooIndices = torch::empty({2, (int64_t)Edges.size()}, Int64Ty);
  auto CooIndicesRef = CooIndices.accessor<int64_t, 2>();
  for (unsigned i = 0; i < Edges.size(); i++) {
    if (Flip) {
      CooIndicesRef[1][i] = (int64_t)Edges[i].Src;
      CooIndicesRef[0][i] = (int64_t)Edges[i].Dest;
    } else {
      CooIndicesRef[0][i] = (int64_t)Edges[i].Src;
      CooIndicesRef[1][i] = (int64_t)Edges[i].Dest;
    }
  }
  return torch::sparse_coo_tensor(CooIndices,
                                  torch::ones({(int64_t)Edges.size()}), {N, M});
}

torch::Tensor BatchedGraphBuilder::getBatched(bool Flip) const {
  return buildAdjacencyMat(Edges, N, M, Flip);
}
