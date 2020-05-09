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
    : NumValues(Frt.num_values()), NumUses(Frt.num_uses()),
      FocusId(Frt.focus_id()), Use1(getEdges(Frt.use1())),
      Use2(getEdges(Frt.use2())), MemRefs(getEdges(Frt.mem_refs())),
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

void ProcessedVectorPack::proto(serialize::VectorPack &VP) const {
  serialize::VectorPack::Kind Kind;
  switch (K) {
  case General:
    Kind = serialize::VectorPack::GENERAL;
    break;
  case Store:
    Kind = serialize::VectorPack::STORE;
    break;
  case Load:
    Kind = serialize::VectorPack::LOAD;
    break;
  }
  VP.set_kind(Kind);
  VP.set_inst_id(InstId);
  for (int64_t L : Lanes)
    VP.add_lanes(L);
}

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

namespace {

// Aux. class to build up a graph representation in protobuf.
class GraphSerializer {
  serialize::Frontier::Graph *G;

protected:
  void addEdge(unsigned Src, unsigned Dest) {
    G->add_sources(Src);
    G->add_sources(Dest);
  }
  // This is a nop because we will serialize one frontier at a time
  void finishBatch(unsigned, unsigned) {}

public:
  serialize::Frontier::Graph *setGraph(serialize::Frontier::Graph *GG) {
    return G = GG;
  }
};

} // namespace

void PolicyWriter::write(const Frontier *Frt, Packer *Pkr,
                         ArrayRef<const VectorPack *> Packs,
                         ArrayRef<float> Prob, unsigned MaxNumLanes) {
  serialize::Supervision S;
  auto *ProtoFrt = new serialize::Frontier();

  FrontierPreprocessor<GraphSerializer> Serializer(MaxNumLanes);

  // Tell the serializer where to dump the edges while traversing the frontier.
  ProtoFrt->set_allocated_use1(
      Serializer.use1().setGraph(new serialize::Frontier::Graph()));
  ProtoFrt->set_allocated_use2(
      Serializer.use2().setGraph(new serialize::Frontier::Graph()));
  ProtoFrt->set_allocated_mem_refs(
      Serializer.memRefs().setGraph(new serialize::Frontier::Graph()));
  ProtoFrt->set_allocated_independence(
      Serializer.independence().setGraph(new serialize::Frontier::Graph()));
  ProtoFrt->set_allocated_inv_unresolved(
      Serializer.invUnresolved().setGraph(new serialize::Frontier::Graph()));
  for (auto &Unresolved : Serializer.unresolved())
    Unresolved.setGraph(ProtoFrt->add_unresolved());

  IRIndex Index(Frt);

  // Traverse the frontier and dump the edges to `S`.
  unsigned NumValues, NumUses;
  Serializer.process(Frt, Index, Pkr, NumValues, NumUses);

  ProtoFrt->set_num_values(NumValues);
  ProtoFrt->set_num_uses(NumUses);

  // Dump opcode (taking type into account) of the values.
  auto ValueTypes = getValueTypes(Index);
  for (int64_t Ty : ValueTypes)
    ProtoFrt->add_value_types(Ty);

  Instruction *Focus = Frt->getNextFreeInst();
  assert(Focus && "Attempting to serialize empty frontier");
  ProtoFrt->set_focus_id(Index.getValueId(Focus));

  S.set_allocated_frontier(ProtoFrt);
  google::protobuf::util::SerializeDelimitedToZeroCopyStream(S, &OS);
}
