/*
 * This file provides the utility to serialize a target policy,
 * which consists of a frontier and the pack distribution
 * determined by the target policy.
 *
 * Notice that the writer writes a raw/unprocessed frontier and packs
 * while the reader reads out a processed frontier and packs.
 * The reason is that it's easier to directly serialize a raw frontier,
 * skipping the processing step.
 */
#ifndef SERIALIZE_H
#define SERIALIZE_H
#include "IRModel.h"
#include "Preprocessing.h"
#include "Proto/serialize.pb.h"
#include "google/protobuf/util/delimited_message_util.h"
#include <google/protobuf/io/zero_copy_stream_impl.h>

// A frontier processed into a bunch of adjacency matrices --
// in order to be consumed by a graph neural network,
// describing things like unresolved uses and use edges.
struct ProcessedFrontier {
  unsigned NumValues;
  unsigned NumUses;
  unsigned FocusId;
  std::vector<DiEdge> Use1, Use2, MemRefs, Independence, InvUnresolved;
  std::vector<std::vector<DiEdge>> Unresolved;
  std::vector<int32_t> ValueTypes;

  ProcessedFrontier(const serialize::Frontier &);
};

struct ProcessedVectorPack {
  enum Kind { General, Store, Load };

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
  bool read(PolicySupervision &PS) {
    serialize::Supervision S;
    bool CleanEOF;
    bool Success = google::protobuf::util::ParseDelimitedFromZeroCopyStream(
        &S, &IS, &CleanEOF);
    PS = S;
    return Success;
  }
};

class PolicyWriter {
  google::protobuf::io::FileOutputStream OS;

public:
  PolicyWriter(int FD) : OS(FD) { OS.SetCloseOnDelete(true); }
  void write(const Frontier *, Packer *, llvm::ArrayRef<const VectorPack *>,
             llvm::ArrayRef<float> Prob, PackingModel Model);
};
#endif // SERIALIZE_H
