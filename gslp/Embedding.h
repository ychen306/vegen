#include "llvm/ADT/Optional.h"
#include "llvm/ADT/DenseMap.h"
#include <vector>

namespace llvm {
class Value;
class Constant;
class BasicBlock;
class Instruction;
class DataLayout;
class TargetLibraryInfo;
} // namespace llvm

struct Embedding : public std::vector<float> {
  float S;

public:
  Embedding(float S) : S(S){};
  // The metric
  float operator-(const Embedding &) const;
};

llvm::raw_ostream &operator<<(llvm::raw_ostream &OS, const Embedding &);

class AffineEmbedder {
  llvm::BasicBlock *BB;
  const llvm::DataLayout *DL;
  llvm::Constant *evaluate(llvm::Instruction *Out,
                           std::vector<llvm::Value *> LiveIns,
                           std::vector<llvm::Constant *> LiveInVals) const;
  const float S;

public:
  AffineEmbedder(float S, llvm::BasicBlock *BB, const llvm::DataLayout *DL)
      : S(S), BB(BB), DL(DL) {}
  AffineEmbedder(llvm::BasicBlock *BB, const llvm::DataLayout *DL)
      : S(10), BB(BB), DL(DL) {}
  llvm::Optional<Embedding> embed(llvm::Instruction *,
                                  bool Signed = true) const;
};

// Here comes that templatey feeling again
template <class EmbedderTy> class Metricizer {
  float MaxDist;
  EmbedderTy Embedder;
  llvm::DenseMap<llvm::Instruction *, llvm::Optional<Embedding>> Embeddings;
  llvm::Optional<Embedding> getEmbedding(llvm::Instruction *I) {
    auto It = Embeddings.find(I);
    if (It != Embeddings.end())
      return It->second;
    auto E = Embedder.embed(I);
    return Embeddings[I] = E;
  }
public:
  Metricizer(EmbedderTy Embedder, float MaxDist=1e9) : Embedder(Embedder), MaxDist(MaxDist) {}
  float getDistance(llvm::Instruction *I1, llvm::Instruction *I2) {
    auto E1OrNull = getEmbedding(I1);
    auto E2OrNull = getEmbedding(I2);
    if (!E1OrNull || !E2OrNull || E1OrNull->size() != E2OrNull->size())
      return MaxDist;
    auto E1 = *E1OrNull;
    auto E2 = *E2OrNull;
    return (E1 - E2);
  }
};
