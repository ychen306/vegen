#ifndef EXPR_HASHER_H
#define EXPR_HASHER_H

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"

namespace llvm {
class Instruction;
class Type;
class Value;
} // namespace llvm

class Canonicalizer {
public:
  // an equivalence class of syntactically equivalent expression
  struct Node {
    llvm::DenseSet<llvm::Instruction *> Members;

    // get one arbitrary member (if there's any)
    llvm::Instruction *getOneMember() const {
      return Members.empty() ? nullptr : *Members.begin();
    }
  };

private:
  using NodeSignature =
      std::tuple<llvm::Type *, unsigned /*opcode*/, Node *, Node *, Node *>;
  llvm::DenseMap<NodeSignature, std::unique_ptr<Node>> Nodes;
  Node *getNodeForValue(llvm::Value *);
  Node *getOrCreate(NodeSignature);

public:
  Node *get(llvm::Instruction *);
};
#endif // end EXPR_HASHER_H
