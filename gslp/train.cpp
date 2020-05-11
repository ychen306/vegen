#include "GraphUtil.h"
#include "IRModel.h"
#include "IRVec.h"
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

static cl::opt<unsigned>
    EmbSize("emb-size", cl::value_desc("Size of embedding"), cl::init(64));

static cl::opt<unsigned> MsgPassingIters(
    "msg-passing-iters",
    cl::value_desc("Number of iterations we do message passing"), cl::init(8));

namespace {

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

  BatchedFrontier Batched;

  unsigned NumValues = 0;
  unsigned NumUses = 0;
  // Here we go.
  for (auto *PS : Supervisions) {
    const ProcessedFrontier &Frt = PS->Frt;
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

static
torch::Tensor computeProb(PackingModel Model, const PackDistribution &PD,
                const PolicySupervision *S) {
  std::vector<torch::Tensor> Prob;
  auto &Frt = S->Frt;
  unsigned FocusId = Frt.FocusId;
  for (const auto &Pack : S->Packs) {
    if (Pack.K == ProcessedVectorPack::Scalar) {
      // Scalar (i.e., nop).
      Prob.push_back(PD.OpProb[FocusId][Model->getNopId()]);
    } else {
      // T involves an actual pack.
      // We pretend we can sample the opcode and lanes independently
      auto PackProb = PD.OpProb[FocusId][Pack.InstId];
      unsigned i = 0;
      for (uint64_t j : Pack.Lanes)
        PackProb *= PD.LaneProbs[i++][FocusId][j];
      Prob.push_back(PackProb);
    }
  }
  auto Predicted = torch::stack(Prob);
  return Predicted / Predicted.sum();
}

// Given a bunch of vectors Xs (B x N) and a bunch of indices Is (B x M),
// return a flat tensor with shape `sum_i M_i`.
class BatchSelector {
  torch::Device Device;
  unsigned N;
  std::vector<torch::Tensor> Xs;
  std::vector<int64_t> I;
public:
  BatchSelector(torch::Device Device) : Device(Device), N(0) {
    Xs.push_back(torch::zeros({1}).to(Device));
  }
  void addBatch(torch::Tensor X, llvm::ArrayRef<int64_t> Indices) {
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
  torch::Tensor get() {
    auto IdxTensor = torch::from_blob(
        I.data(), {(int64_t)I.size()}, 
        torch::TensorOptions().dtype(torch::kInt64)).clone();
    return torch::cat(Xs).index(IdxTensor).to(Device);
  }
};

std::vector<torch::Tensor> computeProbInBatch(
    PackingModel Model,
    llvm::ArrayRef<PackDistribution> PDs,
    llvm::ArrayRef<const PolicySupervision *> Supervisions) {
  unsigned N = PDs.size();
  std::vector<torch::Tensor> OpProbs;

  torch::Device CPU(torch::kCPU);

  BatchSelector BatchOpProb(CPU);
  std::vector<BatchSelector> BatchLaneProbs;
  for (unsigned i = 0; i < MaxNumLanes; i++)
    BatchLaneProbs.emplace_back(CPU);

  for (unsigned i = 0; i < N; i++) {
    const auto &PD = PDs[i];
    const auto &Frt = Supervisions[i]->Frt;

    // Compute op prob for the packs
    auto OpProb = PD.OpProb[Frt.FocusId];
    std::vector<int64_t> OpIds;
    for (auto &Pack : Supervisions[i]->Packs) {
      if (Pack.K == ProcessedVectorPack::Scalar)
        OpIds.push_back(Model->getNopId());
      else
        OpIds.push_back(Pack.InstId);
    }
    BatchOpProb.addBatch(OpProb.log(), OpIds);

    // Compute lane prob for all the packs.
    for (unsigned j = 0; j < MaxNumLanes; j++) {
      auto LaneProb = PD.LaneProbs[j][Frt.FocusId];
      std::vector<int64_t> ValueIds;
      for (auto &Pack : Supervisions[i]->Packs) {
        if (j < Pack.Lanes.size())
          ValueIds.push_back(Pack.Lanes[j]);
        else
          ValueIds.push_back(-1);
      }
      BatchLaneProbs[j].addBatch(LaneProb.log(), ValueIds);
    }
  }
  auto RawLogProb = BatchOpProb.get();
  for (auto &LP : BatchLaneProbs)
    RawLogProb = RawLogProb + LP.get();
  auto RawProb = RawLogProb.exp();

  // Unpack the flatten probs and renormalize them.
  std::vector<torch::Tensor> Probs;
  unsigned Offset = 0;
  for (unsigned i = 0; i < N; i++) {
    unsigned M = Supervisions[i]->Packs.size();
    auto Prob = RawProb.slice(0/*dim*/, Offset, Offset+M);
    Probs.push_back(Prob / Prob.sum());
    Offset += M;
  }
  return Probs;
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

  // FIXME:
  // make the number of instruction a configurable thing (w/ a config file?)
  // and allow constructing a model w/ just the number of instruction w/o
  // telling it what the instructions are.
  static IRInstTable VecBindingTable;
  PackingModel Model(EmbSize, VecBindingTable.getBindings(), MaxNumLanes);
  torch::Device Device(torch::kCPU);
  if (torch::cuda::is_available())
    Device = torch::Device(torch::kCUDA);

  Model->to(Device);
#if 1
  {
    Timer T("train", "Time takes to do backward on a batch of 16 frontiers");
    int FD;
    ExitOnError ExitOnErr("Error: ");
    std::error_code EC = sys::fs::openFileForRead(InputFileName, FD);
    ExitOnErr(errorCodeToError(EC));

    PolicyReader Reader(FD);
    PackingDataset Dataset(Reader);

    std::vector<const PolicySupervision *> Supervisions;
    for (unsigned i = 0; i < std::min<unsigned>(8, Dataset.size().value()); i++)
      Supervisions.push_back(Dataset.get(i));

    auto Batch = batch(Supervisions);
    auto &Frt = Batch.first;
    auto &Sup = Batch.second;

    auto PDs = Model->batch_forward(Frt, Device, None /* We don't have IR indexes */,
        8);

    T.startTimer();
    unsigned i = 0;
    std::vector<torch::Tensor> Losses;
#if 0
    for (auto PD : PDs) {
      auto Target = torch::from_blob(const_cast<float *>(Sup[i]->Prob.data()), {(int64_t)Sup[i]->Prob.size()},
                       torch::TensorOptions().dtype(torch::kFloat32));
      auto Predicted = computeProb(Model, PD, Sup[i]);
      auto Loss = -Target.dot(Predicted.log());
      Losses.push_back(Loss);
      i++;
    }
#else
    auto Probs = computeProbInBatch(Model, PDs, Sup);
    for (unsigned i = 0; i < PDs.size(); i++) {
      auto Target = torch::from_blob(const_cast<float *>(Sup[i]->Prob.data()), {(int64_t)Sup[i]->Prob.size()},
          torch::TensorOptions().dtype(torch::kFloat32));
      auto Predicted = Probs[i];
      auto Loss = -Target.dot(Predicted.log());
      Losses.push_back(Loss);
    }
#endif
    torch::stack(Losses).sum().backward();
    
    T.stopTimer();
    return 0;
  }
#endif


  for (auto &Batch : *DataLoader) {
    errs() << "!!!\n";
    auto &Frt = Batch.first;
    auto &Sup = Batch.second;
    std::vector<PackDistribution> PDs =
      Model->batch_forward(Frt, Device, None /* We don't have IR indexes */,
        MsgPassingIters);
  
    auto Probs = computeProbInBatch(Model, PDs, Sup);
    std::vector<torch::Tensor> Losses;
    for (unsigned i = 0; i < PDs.size(); i++) {
      auto Target = torch::from_blob(const_cast<float *>(Sup[i]->Prob.data()), {(int64_t)Sup[i]->Prob.size()},
          torch::TensorOptions().dtype(torch::kFloat32));
      auto Predicted = Probs[i];
      auto Loss = -Target.dot(Predicted.log());
      Losses.push_back(Loss);
    }
    torch::stack(Losses).sum().backward();
  }
}
