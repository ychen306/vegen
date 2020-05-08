#ifndef SERIALIZE_H
#define SERIALIZE_H
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
};

struct ProcessedVectorPack {
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
