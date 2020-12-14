#include "llvm/ADT/Optional.h"
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
  Embedding(float S) : S(S) {};
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
  llvm::Optional<Embedding> embed(llvm::Instruction *, bool Signed=true) const;
};
