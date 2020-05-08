#ifndef SERIALIZE_H
#define SERIALIZE_H
#include "Preprocessing.h"
#include "Proto/serialize.pb.h"
#include <google/protobuf/io/zero_copy_stream_impl.h>


/*
 * This file provides the utility to serialize a target policy,
 * which consists of a frontier and the pack distribution
 * determined by the target policy.
 */

// A frontier processed into a bunch of adjacency matrices --
// in order to be consumed by a graph neural network,
// describing things like unresolved uses and use edges.
struct ProcessedFrontier {
  unsigned NumValues;
  unsigned FocusId;
  std::vector<DiEdge> Use1, Use2, MemRefs, Independence, InvUnresolved;
  std::vector<std::vector<DiEdge>> Unresolved;
  std::vector<int32_t> ValueTypes;

  ProcessedFrontier(const serialize::Frontier &);
};

struct ProcessedVectorPack {
  enum Kind {
    General, Store, Load
  };

  Kind K;
  unsigned InstId;
  std::vector<int64_t> Lanes;

  ProcessedVectorPack(const serialize::VectorPack &);
};

struct PolicySupervision {
  ProcessedFrontier Frt;
  std::vector<ProcessedVectorPack> Packs;
  std::vector<float> Prob;

  PolicySupervision(const serialize::Supervision &);
};

class PolicyReader {
  google::protobuf::io::FileInputStream IS;
public:
  PolicyReader(int FD) : IS(FD) { IS.SetCloseOnDelete(true); }
  void read(std::vector<ProcessedFrontier> &,
      std::vector<ProcessedVectorPack> &);
};

class PolicyWriter {
  google::protobuf::io::FileOutputStream OS;
public:
  PolicyWriter(int FD) : OS(FD) {OS.SetCloseOnDelete(true);}
  void writeOne(const ProcessedFrontier &, const ProcessedVectorPack &);
};
#endif // SERIALIZE_H
