#ifndef PREPROCESSING_H
#define PREPROCESSING_H

/*
 * This file provides utility to preprocess/abstract
 * a frontier into a bunch of graphs
 * that's easier for serialization or network evaluation.
 */

#include "Packer.h"
#include "Solver.h"
#include "llvm/IR/Instruction.h"

struct DiEdge {
  unsigned Src, Dest;
  DiEdge(unsigned S, unsigned T) : Src(S), Dest(T) {}
};

class IRIndex {
  llvm::DenseMap<llvm::Value *, unsigned> Value2IdMap;
  std::vector<llvm::Value *> Values;

  void trackValue(llvm::Value *);

public:
  IRIndex(llvm::Function &F);
  IRIndex(const Frontier *Frt);
  unsigned getValueId(llvm::Value *V) const { return Value2IdMap.lookup(V); }
  llvm::Value *get(unsigned i) const { return Values[i]; }
  unsigned getNumValues() const { return Values.size(); }
};

template <typename Builder> struct BatchedUseGraph1 : public Builder {
  void process(const IRIndex &Index) {
    using namespace llvm;
    unsigned N = Index.getNumValues();
    for (unsigned i = 0; i < N; i++) {
      auto *V = Index.get(i);
      auto *I = dyn_cast<Instruction>(V);
      if (!I)
        continue;
      if (I->getNumOperands() < 1)
        continue;
      Builder::addEdge(Index.getValueId(I), Index.getValueId(I->getOperand(0)));
    }
    Builder::finishBatch(N, N);
  }
};

template <typename Builder> struct BatchedUseGraph2 : public Builder {
  void process(const IRIndex &Index) {
    using namespace llvm;

    unsigned N = Index.getNumValues();
    for (unsigned i = 0; i < N; i++) {
      auto *V = Index.get(i);
      auto *I = dyn_cast<Instruction>(V);
      if (!I)
        continue;
      if (I->getNumOperands() < 1)
        continue;
      Builder::addEdge(Index.getValueId(I), Index.getValueId(I->getOperand(0)));
    }
    Builder::finishBatch(N, N);
  }
};

template <typename Builder> class BatchedMemRefGraph : public Builder {
  void getEdges(const IRIndex &Index, ConsecutiveAccessDAG &AccessDAG) {
    for (auto &LeftAndRights : AccessDAG) {
      auto *Left = LeftAndRights.first;
      auto &Rights = LeftAndRights.second;
      unsigned LeftId = Index.getValueId(Left);
      for (auto *Right : Rights) {
        unsigned RightId = Index.getValueId(Right);
        Builder::addEdge(LeftId, RightId);
      }
    }
  }

public:
  void process(const IRIndex &Index, ConsecutiveAccessDAG &LoadDAG,
               ConsecutiveAccessDAG &StoreDAG) {
    getEdges(Index, LoadDAG);
    getEdges(Index, StoreDAG);
    unsigned N = Index.getNumValues();
    Builder::finishBatch(N, N);
  }
};

template <typename Builder> struct BatchedIndependenceGraph : public Builder {
  void process(const Frontier *Frt, Packer *Pkr, const IRIndex &Index) {
    using namespace llvm;

    auto *BB = Frt->getBasicBlock();
    auto *VPCtx = Pkr->getContext(BB);
    auto &LDA = Pkr->getLDA(BB);

    const BitVector &FreeInsts = Frt->getFreeInsts();

    for (auto I = BB->begin(), E = BB->end(); I != E; ++I) {
      if (!Frt->isFree(&*I))
        continue;
      BitVector Independent = LDA.getIndependent(&*I);
      Independent &= FreeInsts;

      unsigned i = Index.getValueId(&*I);
      for (auto *V : VPCtx->iter_values(Independent)) {
        unsigned ValId = Index.getValueId(V);
        Builder::addEdge(i, ValId);
        Builder::addEdge(ValId, i);
      }
    }
    unsigned N = Index.getNumValues();
    Builder::finishBatch(N, N);
  }
};

template <typename Builder> class BatchedUnresolvedUseGraph : public Builder {
  unsigned LaneId;

public:
  BatchedUnresolvedUseGraph(unsigned LaneId) : LaneId(LaneId) {}
  void process(const Frontier *Frt, Packer *Pkr, const IRIndex &Index) {
    using namespace llvm;

    BasicBlock *BB = Frt->getBasicBlock();
    llvm::ArrayRef<const OperandPack *> UnresolvedPacks =
        Frt->getUnresolvedPacks();

    // Include unresolved vector uses
    for (unsigned i = 0; i < UnresolvedPacks.size(); i++) {
      const OperandPack &OP = *UnresolvedPacks[i];
      if (LaneId >= OP.size())
        continue;
      auto *V = OP[LaneId];
      auto *I = dyn_cast<Instruction>(V);
      // Skip `I` is frozen (and therefore resolved)
      if (!I || I->getParent() != BB || !Frt->isFree(I))
        continue;
      Builder::addEdge(i, Index.getValueId(I));
    }

    if (LaneId == 0) {
      unsigned i = UnresolvedPacks.size();
      // Include unresolved scalar uses
      for (auto *V : Frt->getUnresolvedScalars()) {
        // Pretend scalar uses are degenerate vector use
        // and assign them to the first lane.
        Builder::addEdge(i++, Index.getValueId(V));
      }
    }

    unsigned NumUnresolvedUses =
        UnresolvedPacks.size() + Frt->numUnresolvedScalars();
    Builder::finishBatch(NumUnresolvedUses, Index.getNumValues());
  }
};

template <typename Builder>
struct BatchedInverseUnresolvedUseGraph : public Builder {
  void process(const Frontier *Frt, Packer *Pkr, const IRIndex &Index) {
    using namespace llvm;

    BasicBlock *BB = Frt->getBasicBlock();
    auto UnresolvedPacks = Frt->getUnresolvedPacks();
    // Include unresolved vector uses
    for (unsigned i = 0; i < UnresolvedPacks.size(); i++) {
      const OperandPack &OP = *UnresolvedPacks[i];
      for (auto *V : OP) {
        auto *I = dyn_cast<Instruction>(V);
        // Skip `I` is frozen (and therefore resolved)
        if (!I || I->getParent() != BB || !Frt->isFree(I))
          continue;
        Builder::addEdge(Index.getValueId(I), i);
      }
    }

    unsigned i = UnresolvedPacks.size();
    // Include unresolved scalar uses
    for (auto *V : Frt->getUnresolvedScalars()) {
      // Pretend scalar uses are degenerate vector use
      // and assign them to the first lane.
      Builder::addEdge(Index.getValueId(V), i++);
    }

    unsigned NumUnresolvedUses = i;
    Builder::finishBatch(Index.getNumValues(), NumUnresolvedUses);
  }
};

template <typename Builder> class FrontierPreprocessor {
  BatchedUseGraph1<Builder> UseGraph1Builder;
  BatchedUseGraph2<Builder> UseGraph2Builder;
  BatchedMemRefGraph<Builder> MemRefGraphBuilder;
  BatchedIndependenceGraph<Builder> IndependenceGraphBuilder;
  std::vector<BatchedUnresolvedUseGraph<Builder>> UnresolvedGraphBuilders;
  BatchedInverseUnresolvedUseGraph<Builder> InvUnresolvedGraphBuilder;

public:
  FrontierPreprocessor(unsigned MaxNumLanes) {
    for (unsigned i = 0; i < MaxNumLanes; i++)
      UnresolvedGraphBuilders.emplace_back(i);
  }

  void process(const Frontier *Frt, const IRIndex &Index, Packer *Pkr,
               unsigned &NumValues, unsigned &NumUses) {
    using namespace llvm;

    BasicBlock *BB = Frt->getBasicBlock();
    auto &LoadDAG = Pkr->getLoadDAG(BB);
    auto &StoreDAG = Pkr->getStoreDAG(BB);

    UseGraph1Builder.process(Index);
    UseGraph2Builder.process(Index);
    MemRefGraphBuilder.process(Index, LoadDAG, StoreDAG);
    IndependenceGraphBuilder.process(Frt, Pkr, Index);
    InvUnresolvedGraphBuilder.process(Frt, Pkr, Index);
    for (auto &B : UnresolvedGraphBuilders)
      B.process(Frt, Pkr, Index);

    NumValues = Index.getNumValues();
    NumUses = Frt->getUnresolvedPacks().size() + Frt->numUnresolvedScalars();
  }

  BatchedUseGraph1<Builder> &use1() { return UseGraph1Builder; }
  BatchedUseGraph2<Builder> &use2() { return UseGraph2Builder; }
  BatchedMemRefGraph<Builder> &memRefs() {
    return MemRefGraphBuilder;
  }
  BatchedIndependenceGraph<Builder> &independence() {
    return IndependenceGraphBuilder;
  }
  BatchedInverseUnresolvedUseGraph<Builder> &invUnresolved() {
    return InvUnresolvedGraphBuilder;
  }
  std::vector<BatchedUnresolvedUseGraph<Builder>> &unresolved() {
    return UnresolvedGraphBuilders;
  }
};

class OpcodeTable {
  static unsigned getUnknownTypeId() { return 0; }
  static unsigned getConstId() { return 1; }
  static unsigned getCastId() { return 2; }
  static unsigned getBitwidth(llvm::Type *Ty) {
    using namespace llvm;

    if (auto *IntTy = dyn_cast<IntegerType>(Ty))
      return IntTy->getBitWidth();
    if (Ty->isFloatTy())
      return 32;
    if (Ty->isDoubleTy())
      return 64;
    return 0; // don't care
  }

  static std::vector<unsigned> Bitwidths;
  static std::vector<unsigned> Opcodes;
  std::map<std::pair<unsigned, unsigned>, unsigned> ValueTypeIds;

public:
  OpcodeTable();
  unsigned getNumValueTypes() const {
    // # of value types = <# inst opcode> * <# bitwidths> + <constant> + <cast>
    // <unknown>
    return Opcodes.size() * Bitwidths.size() + 1 + 1 + 1;
  }

  unsigned getValueTypeId(llvm::Value *V) const;
};

extern OpcodeTable OpTable;

std::vector<int64_t> getValueTypes(llvm::ArrayRef<IRIndex> Indexes);
#endif // PREPROCESSING_H
