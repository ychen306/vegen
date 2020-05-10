#include "GraphUtil.h"
#include "Serialize.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/GlobPattern.h"
#include "llvm/Support/Timer.h"
#include "llvm/Support/raw_ostream.h"
#include <torch/torch.h>

using namespace llvm;

static cl::opt<std::string> InputFileName(cl::Positional,
                                          cl::value_desc("Input file name"));

static cl::opt<unsigned>
    MaxNumLanes("max-num-lanes",
                cl::value_desc("Max number of lanes in a vector"), cl::init(8));

static cl::opt<unsigned> BatchSize("batch-size", cl::value_desc("Batch size"),
                                   cl::init(8));

static cl::opt<unsigned>
    NumWorkers("num-workers", cl::value_desc("Number of data-loader workers"),
               cl::init(1));

namespace {

struct BatchedFrontier {
  unsigned NumValues;
  unsigned NumUses;
  torch::Tensor Use1;
  torch::Tensor Use2;
  torch::Tensor LeftMemRef;
  torch::Tensor RightMemRef;
  torch::Tensor Independence;
  torch::Tensor InvUnresolved;
  std::vector<torch::Tensor> Unresolved;
  torch::Tensor ValueTypes;
};

class PackingDataset
    : public torch::data::Dataset<PackingDataset, const PolicySupervision *> {
  std::vector<PolicySupervision> Supervisions;

public:
  PackingDataset(PolicyReader &Reader);
  const PolicySupervision *get(size_t i) override { return &Supervisions[i]; }
  c10::optional<size_t> size() const override { return Supervisions.size(); }
};

// Add a util func that allows us to take a whole array of edges
struct GraphBatcher : public BatchedGraphBuilder {
  void addGraph(llvm::ArrayRef<DiEdge> NewEdges, unsigned N, unsigned M);
};

} // end anonymous namespace

PackingDataset::PackingDataset(PolicyReader &Reader) {
  PolicySupervision PS;
  while (Reader.read(PS))
    Supervisions.push_back(std::move(PS));
}

void GraphBatcher::addGraph(llvm::ArrayRef<DiEdge> NewEdges, unsigned N,
                            unsigned M) {
  for (auto &E : NewEdges)
    addEdge(E.Src, E.Dest);
  finishBatch(N, M);
}

static std::pair<BatchedFrontier, std::vector<const PolicySupervision *>>
batch(std::vector<const PolicySupervision *> Supervisions) {
  GraphBatcher Use1;
  GraphBatcher Use2;
  GraphBatcher MemRef;
  GraphBatcher RightMemRef;
  GraphBatcher Independence;
  GraphBatcher InvUnresolved;
  std::vector<GraphBatcher> Unresolved(MaxNumLanes);
  std::vector<int64_t> ValueTypes;

  unsigned NumValues = 0;
  unsigned NumUses = 0;
  // Here we go.
  for (auto *PS : Supervisions) {
    const ProcessedFrontier &Frt = PS->Frt;
    unsigned N = Frt.NumValues, M = Frt.NumUses;
    NumValues += N;
    NumUses += M;

    Use1.addGraph(Frt.Use1, N, N);
    Use2.addGraph(Frt.Use2, N, N);
    MemRef.addGraph(Frt.MemRefs, N, N);
    Independence.addGraph(Frt.Independence, N, N);
    InvUnresolved.addGraph(Frt.InvUnresolved, N, M);
    for (unsigned i = 0; i < MaxNumLanes; i++)
      Unresolved[i].addGraph(Frt.Unresolved[i], M, N);

    ValueTypes.insert(ValueTypes.end(), Frt.ValueTypes.begin(),
                      Frt.ValueTypes.end());
  }

  auto ValueTypeTensor =
      torch::from_blob(ValueTypes.data(), {(int64_t)ValueTypes.size()},
                       torch::TensorOptions().dtype(torch::kInt64))
          .clone();

  BatchedFrontier Batched;
  Batched.NumValues = NumValues;
  Batched.NumUses = NumUses;
  Batched.Use1 = Use1.getBatched();
  Batched.Use2 = Use2.getBatched();
  Batched.LeftMemRef = MemRef.getBatched();
  Batched.RightMemRef = MemRef.getBatched(true/*flip edges*/);
  Batched.Independence = Independence.getBatched();
  Batched.InvUnresolved = InvUnresolved.getBatched();
  Batched.ValueTypes = ValueTypeTensor;
  for (unsigned i = 0; i < MaxNumLanes; i++)
    Batched.Unresolved.push_back(Unresolved[i].getBatched());

  return {Batched, std::move(Supervisions)};
}

int main(int argc, char **argv) {
  cl::ParseCommandLineOptions(argc, argv);

  int FD;
  ExitOnError ExitOnErr("Error: ");
  std::error_code EC = sys::fs::openFileForRead(InputFileName, FD);
  ExitOnErr(errorCodeToError(EC));

  PolicyReader Reader(FD);
  PackingDataset Dataset(Reader);

  // What a beautiful piece of code.
  using TransformTy = torch::data::transforms::BatchLambda<
      std::vector<const PolicySupervision *>,
      std::pair<BatchedFrontier, std::vector<const PolicySupervision *>>>;
  auto DataLoaderOpt =
      torch::data::DataLoaderOptions().batch_size(BatchSize).workers(
          NumWorkers);
  auto DataLoader =
      torch::data::make_data_loader<torch::data::samplers::RandomSampler>(
          Dataset.map(TransformTy(batch)), DataLoaderOpt);

  for (auto &Batch : *DataLoader) {
    errs() << "BATCH\n";
  }
}
