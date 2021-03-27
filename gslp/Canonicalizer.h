#ifndef EXPR_HASHER_H
#define EXPR_HASHER_H

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/PointerUnion.h"
#include "llvm/Support/RandomNumberGenerator.h"
#include "llvm/Support/raw_ostream.h"

namespace llvm {
class Instruction;
class Type;
class Value;
} // namespace llvm

class Canonicalizer {
public:
  using HashType = uint64_t;
  struct Node {
    llvm::Type *Ty;
    unsigned Opcode;
    HashType Hash;
    Node *Arg1, *Arg2, *Arg3;
    llvm::Value *Rep; // representative of this expression

    // leaf node
    Node(llvm::Type *Ty)
        : Ty(Ty), Opcode(0), Hash(0), Arg1(nullptr), Arg2(nullptr), Arg3(nullptr), Rep(nullptr) {}
  };

  struct NodeHashInfo {
    static inline Node getEmptyKey() { return Node(nullptr); }

    static inline Node getTombstoneKey() { return Node((llvm::Type *)~0ull); }

    static inline bool isEqual(const Node &N1, const Node &N2) {
      return std::tie(N1.Ty, N1.Opcode, N1.Arg1, N1.Arg2, N1.Arg3) ==
             std::tie(N2.Ty, N2.Opcode, N2.Arg1, N2.Arg2, N2.Arg3);
    }

    static unsigned getHashValue(const Node &N) { return N.Hash; }
  };

private:
  std::unique_ptr<llvm::RandomNumberGenerator> RNG;
  llvm::DenseMap<unsigned, HashType> OpcodeHashes;
  llvm::DenseMap<llvm::Type *, HashType> LeafHashes;

  llvm::DenseMap<Node, std::unique_ptr<Node>, NodeHashInfo> Nodes;

  Node *canonicalize(const Node &);

  HashType hashLeaf(llvm::Type *);
  HashType hashOpcode(unsigned Opcode);

  Node *getNodeForValue(llvm::Value *);

public:
  Canonicalizer(decltype(RNG) RNG) : RNG(std::move(RNG)) {}
  Node *get(llvm::Instruction *);
};
#endif // end EXPR_HASHER_H
