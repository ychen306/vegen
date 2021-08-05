#ifndef USE_DEF_ITERATOR_H
#define USE_DEF_ITERATOR_H

#include "llvm/ADT/GraphTraits.h"
#include "llvm/IR/Value.h"

namespace llvm {

struct DefToUse {
  Value *V;
  DefToUse(Value *V) : V(V) {}
  operator Value *() const { return V; }
  bool operator==(const DefToUse &Other) const { return V == Other.V; }
};

// Provide traits to treat DefToUse as a pointer
template <> struct PointerLikeTypeTraits<DefToUse> {
  static inline void *getAsVoidPointer(DefToUse Def) {
    return reinterpret_cast<void *>(Def.V);
  }
  static inline DefToUse getFromVoidPointer(void *P) {
    return reinterpret_cast<Value *>(P);
  }
  static constexpr int NumLowBitsAvailable = 0;
};

template <> struct GraphTraits<DefToUse> {
  using NodeRef = DefToUse;
  using ChildIteratorType = Value::user_iterator;
  static NodeRef getEntryNode(DefToUse Def) { return Def; }
  static ChildIteratorType child_begin(NodeRef N) { return N.V->user_begin(); }
  static ChildIteratorType child_end(NodeRef N) { return N.V->user_end(); }
};
} // namespace llvm
#endif // USE_DEF_ITERATOR_H
