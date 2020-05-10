#ifndef GRAPH_UTIL_H
#define GRAPH_UTIL_H
#include <torch/torch.h>

struct DiEdge {
  unsigned Src, Dest;
  DiEdge(unsigned S, unsigned T) : Src(S), Dest(T) {}
};

class BatchedGraphBuilder {
  unsigned N, M;
  std::vector<DiEdge> Edges;
public:
  void addEdge(unsigned U, unsigned V) { Edges.emplace_back(U + N, V + M); }
  void finishBatch(unsigned NN, unsigned MM) {
    N += NN;
    M += MM;
  }
  BatchedGraphBuilder() : N(0), M(0) {}
  torch::Tensor getBatched(bool Flip = false) const;
};


#endif // end GRAPH_UTIL_H
