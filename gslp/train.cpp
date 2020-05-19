#include "IRModel.h" // THIS NEEDS TO BE INCLUDED FIRST BECAUSE TORCH SCREWS UP NAMESPACES
#include "GraphUtil.h"
#include "IRVec.h"
#include "ModelUtil.h"
#include "Serialize.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/GlobPattern.h"
#include "llvm/Support/Timer.h"
#include "llvm/Support/raw_ostream.h"
#include <torch/torch.h>

using namespace llvm;

static cl::list<std::string> ArchivePaths(cl::Positional,
                                          cl::value_desc("Input archives"));

static cl::opt<unsigned>
    MaxNumLanes("max-num-lanes",
                cl::value_desc("Max number of lanes in a vector"), cl::init(8));

static cl::opt<unsigned> BatchSize("batch-size", cl::value_desc("Batch size"),
                                   cl::init(32));

static cl::opt<unsigned>
    NumWorkers("num-workers", cl::value_desc("Number of data-loader workers"),
               cl::init(1));

static cl::opt<unsigned>
    EmbSize("emb-size", cl::value_desc("Size of embedding"), cl::init(64));

static cl::opt<unsigned> NumGNNLayers("num-gnn-layers",
                                      cl::value_desc("Number of GNN layers"),
                                      cl::init(8));

static cl::opt<float> LearningRate("lr", cl::value_desc("Learning rate"),
                                   cl::init(1e-2));

static cl::opt<unsigned> NumEpochs("epochs",
                                   cl::value_desc("Number of epochs to train"),
                                   cl::init(5));

static cl::opt<std::string> OutputModelPath("o",
                                            cl::value_desc("Output model path"),
                                            cl::init("model.pt"));

namespace {

class PackingDataset
    : public torch::data::Dataset<PackingDataset, PolicySupervision> {
  std::vector<PolicyArchiveReader> Archives;
  // Prefix sum of the archive size.
  std::vector<size_t> AccumSizes;

public:
  PackingDataset(llvm::ArrayRef<std::string> ArchivePaths) {
    size_t TotalSize = 0;
    for (auto &AP : ArchivePaths) {
      Archives.emplace_back(AP);
      TotalSize += Archives.back().size();
      AccumSizes.push_back(TotalSize);
    }
  }

  PolicySupervision get(size_t i) override {
    // Find the first place in `AccumSizes` greater than i
    auto It = std::upper_bound(AccumSizes.begin(), AccumSizes.end(), i);
    unsigned ArchiveId = It - AccumSizes.begin();
    PolicySupervision PS;
    size_t j;
    if (ArchiveId == 0)
      j = i;
    else
      j = i - AccumSizes[ArchiveId - 1];
    Archives[ArchiveId].read(j, PS);
    return PS;
  }
  c10::optional<size_t> size() const override { return AccumSizes.back(); }
};

// Add a util func that allows us to take a whole array of edges
struct GraphBatcher : public BatchedGraphBuilder {
  void addGraph(llvm::ArrayRef<DiEdge> NewEdges, unsigned N, unsigned M);
};

} // end anonymous namespace

void GraphBatcher::addGraph(llvm::ArrayRef<DiEdge> NewEdges, unsigned N,
                            unsigned M) {
  for (auto &E : NewEdges)
    addEdge(E.Src, E.Dest);
  finishBatch(N, M);
}

static std::pair<BatchedFrontier, std::vector<PolicySupervision>>
batch(std::vector<PolicySupervision> Supervisions) {
  GraphBatcher Use1;
  GraphBatcher Use2;
  GraphBatcher MemRef;
  GraphBatcher RightMemRef;
  GraphBatcher Independence;
  GraphBatcher InvUnresolved;
  std::vector<GraphBatcher> Unresolved(MaxNumLanes);
  std::vector<int64_t> ValueTypes;

  BatchedFrontier Batched;

  unsigned NumValues = 0;
  unsigned NumUses = 0;
  // Here we go.
  for (const auto &PS : Supervisions) {
    const ProcessedFrontier &Frt = PS.Frt;
    unsigned N = Frt.NumValues, M = Frt.NumUses;
    Batched.NumValues.push_back(N);
    Batched.NumUses.push_back(M);
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

  Batched.TotalValues = NumValues;
  Batched.TotalUses = NumUses;
  Batched.Use1 = Use1.getBatched();
  Batched.Use2 = Use2.getBatched();
  Batched.LeftMemRef = MemRef.getBatched();
  Batched.RightMemRef = MemRef.getBatched(true /*flip edges*/);
  Batched.Independence = Independence.getBatched();
  Batched.InvUnresolved = InvUnresolved.getBatched();
  Batched.ValueTypes = ValueTypeTensor;
  for (unsigned i = 0; i < MaxNumLanes; i++)
    Batched.Unresolved.push_back(Unresolved[i].getBatched());

  return {std::move(Batched), std::move(Supervisions)};
}

template <typename OutStreamTy>
void dumpShape(torch::Tensor X, OutStreamTy &Os) {
  for (auto N : X.sizes()) {
    Os << " " << N;
  }
  Os << '\n';
}

static std::vector<torch::Tensor>
computeProbInBatch(PackingModel Model, torch::Device Device,
                   llvm::ArrayRef<PackDistribution> PDs,
                   llvm::ArrayRef<PolicySupervision> Supervisions) {
  BatchPackProbability BPP(MaxNumLanes, Device);
  for (unsigned i = 0; i < PDs.size(); i++) {
    const auto &PD = PDs[i];
    const auto &Frt = Supervisions[i].Frt;

    BPP.start(PD, Frt.FocusId);

    for (auto &Pack : Supervisions[i].Packs) {
      unsigned OpId;
      if (Pack.K == ProcessedVectorPack::Scalar)
        OpId = Model->getNopId();
      else
        OpId = Pack.InstId;
      BPP.addPack(OpId, Pack.Lanes);
    }

    BPP.finish();
  }
  return BPP.get();
}

static void saveModel(PackingModel &Model, std::string ModelPath) {
  torch::serialize::OutputArchive Archive;
  Model->save(Archive);
  Archive.save_to(ModelPath);
}

int main(int argc, char **argv) {
  cl::ParseCommandLineOptions(argc, argv);

  PackingDataset Dataset(ArchivePaths);

  // What a beautiful piece of code.
  using TransformTy = torch::data::transforms::BatchLambda<
      std::vector<PolicySupervision>,
      std::pair<BatchedFrontier, std::vector<PolicySupervision>>>;
  auto DataLoaderOpt =
      torch::data::DataLoaderOptions().batch_size(BatchSize).workers(
          NumWorkers);
  auto DataLoader =
      torch::data::make_data_loader<torch::data::samplers::RandomSampler>(
          Dataset.map(TransformTy(batch)), DataLoaderOpt);

  // FIXME:
  // make the number of instruction a configurable thing (w/ a config file?)
  // and allow constructing a model w/ just the number of instruction w/o
  // telling it what the instructions are.
  static IRInstTable VecBindingTable;
  PackingModel Model(EmbSize, VecBindingTable.getBindings(), MaxNumLanes,
                     NumGNNLayers);
  torch::Device Device(torch::kCPU);
  if (torch::cuda::is_available())
    Device = torch::Device(torch::kCUDA);

  Model->to(Device);
  torch::optim::Adam Optimizer(Model->parameters(),
                               torch::optim::AdamOptions(LearningRate));

  // TODO: checkpoint the model
  for (unsigned Epoch = 0; Epoch < NumEpochs; Epoch++) {
    for (auto &Batch : (*DataLoader)) {
      auto &Frt = Batch.first;
      auto &Supervision = Batch.second;
      std::vector<PackDistribution> PDs = Model->batch_forward(
          Frt, Device, None /* We don't have IR indexes */);

      auto Probs = computeProbInBatch(Model, Device, PDs, Supervision);
      // std::vector<torch::Tensor> Targets;
      std::vector<torch::Tensor> Losses;
      for (unsigned i = 0; i < PDs.size(); i++) {
        // auto Target =
        //    torch::from_blob(const_cast<float *>(Supervision[i].Prob.data()),
        //                     {(int64_t)Supervision[i].Prob.size()},
        //                     torch::TensorOptions().dtype(torch::kFloat32));
        // Targets.push_back(Target);
        auto &Prob = Supervision[i].Prob;
        auto It = std::max_element(Prob.begin(), Prob.end());
        Losses.push_back(-Probs[i][It - Prob.begin()].log());
      }
      // auto Target = torch::cat(Targets).to(Device);
      // auto Predicted = torch::cat(Probs);
      /// auto Loss = -Target.dot(Predicted.log()) / float(Targets.size());
      auto Loss = torch::stack(Losses).mean();

      Optimizer.zero_grad();
      Loss.backward();
      torch::nn::utils::clip_grad_norm_(Model->parameters(), 0.25);
      errs() << "\r " << Loss.item<float>();
      Optimizer.step();
    }
  }
  errs() << '\n';

  saveModel(Model, OutputModelPath);
}
