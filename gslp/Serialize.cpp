#include "Serialize.h"
#include "llvm/ADT/ArrayRef.h"

using namespace llvm;

static std::vector<DiEdge> getEdges(const serialize::Frontier::Graph &G) {
  unsigned N = G.sources_size();
  std::vector<DiEdge> Edges;
  Edges.reserve(N);
  for (unsigned i = 0; i < N; i++)
    Edges.emplace_back(G.sources(i), G.dests(i));
  return Edges;
}

ProcessedFrontier::ProcessedFrontier(const serialize::Frontier &Frt)
    : NumValues(Frt.num_values()), FocusId(Frt.focus_id()),
      Use1(getEdges(Frt.use1())), Use2(getEdges(Frt.use2())),
      MemRefs(getEdges(Frt.mem_refs())),
      Independence(getEdges(Frt.independence())),
      InvUnresolved(getEdges(Frt.inv_unresolved())) {
  for (auto &G : Frt.unresolved())
    Unresolved.push_back(getEdges(G));

  ValueTypes.reserve(Frt.value_types_size());
  for (int32_t Ty : Frt.value_types())
    ValueTypes.push_back(Ty);
}

static void buildGraph(ArrayRef<DiEdge> Edges, serialize::Frontier::Graph &G) {
  for (auto &E : Edges) {
    G.add_sources(E.Src);
    G.add_dests(E.Dest);
  }
}

static serialize::Frontier::Graph *buildGraph(ArrayRef<DiEdge> Edges) {
  auto *G = new serialize::Frontier::Graph();
  buildGraph(Edges, *G);
  return G;
}

void ProcessedFrontier::proto(serialize::Frontier &Frt) const {
  Frt.set_num_values(NumValues);
  Frt.set_focus_id(FocusId);
  Frt.set_allocated_use1(buildGraph(Use1));
  Frt.set_allocated_use2(buildGraph(Use2));
  Frt.set_allocated_mem_refs(buildGraph(MemRefs));
  Frt.set_allocated_independence(buildGraph(Independence));
  Frt.set_allocated_inv_unresolved(buildGraph(InvUnresolved));
  for (auto &G : Unresolved)
    buildGraph(G, *Frt.add_unresolved());
  for (int32_t Ty : ValueTypes)
    Frt.add_value_types(Ty);
}

ProcessedVectorPack::ProcessedVectorPack(const serialize::VectorPack &VP) {
  switch (VP.kind()) {
  case serialize::VectorPack::GENERAL:
    K = General;
    break;
  case serialize::VectorPack::STORE:
    K = Store;
    break;
  case serialize::VectorPack::LOAD:
    K = Load;
    break;
  }
  InstId = VP.inst_id();
  Lanes.reserve(VP.lanes_size());
  for (int64_t L : VP.lanes())
    Lanes.push_back(L);
}

void ProcessedVectorPack::proto(serialize::VectorPack &VP) const {}

PolicySupervision::PolicySupervision(const serialize::Supervision &S)
    : Frt(S.frontier()) {
  Packs.reserve(S.packs_size());
  for (auto &VP : S.packs())
    Packs.emplace_back(VP);
  Prob.reserve(S.prob_size());
  for (float P : S.prob())
    Prob.push_back(P);
}

void PolicySupervision::proto(serialize::Supervision &S) const {
  auto *ProtoFrt = new serialize::Frontier();
  Frt.proto(*ProtoFrt);
  S.set_allocated_frontier(ProtoFrt);

  for (auto &VP : Packs) {
    auto *ProtoPack = S.add_packs();
    VP.proto(*ProtoPack);
  }

  for (auto P : Prob)
    S.add_prob(P);
}
