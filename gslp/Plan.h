#ifndef PLAN_H
#define PLAN_H
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/SmallPtrSet.h"

class VectorPack;
class OperandPack;
class Packer;

namespace llvm {
class Instruction;
class Value;
class BasicBlock;
} // namespace llvm

// VeGen's VPlan
class Plan {
  Packer *Pkr;
  llvm::BasicBlock *BB;
  float Cost;

  llvm::DenseSet<const VectorPack *> Packs;
  // mapping inst -> the pack that contains the inst
  llvm::DenseMap<llvm::Instruction *, const VectorPack *> InstToPackMap;
  using OperandPackSet = llvm::SmallPtrSet<const OperandPack *, 2>;
  // mapping inst -> operands that contains the instruction
  llvm::DenseMap<llvm::Instruction *, OperandPackSet> InstToOperandsMap;
  llvm::DenseMap<llvm::ArrayRef<llvm::Value *>, const VectorPack *>
      ValuesToPackMap;
  llvm::DenseMap<llvm::Instruction *, int> NumUses;
  llvm::DenseMap<const OperandPack *, int> NumOperandUses;
  llvm::DenseMap<const OperandPack *, float> ShuffleCosts;
  
  llvm::Instruction *asInternalInst(llvm::Value *) const;
  bool hasScalarUser(llvm::Instruction *) const;
  float computeShuffleCost(const OperandPack *) const;

  void decUses(llvm::Instruction *);
  void incUses(llvm::Instruction *);
  void updateCostOfVectorUses(llvm::ArrayRef<llvm::Value *>);

public:
  Plan() = delete;
  Plan(Packer *, llvm::BasicBlock *);
  Plan(const Plan &) = default;
  Plan(Plan &&) = default;
  Plan &operator=(const Plan &) = default;

  using PackIterator = decltype(Packs)::const_iterator;
  PackIterator begin() const { return Packs.begin(); }
  PackIterator end() const { return Packs.end(); }

  using OperandIterator = decltype(NumOperandUses)::const_iterator;
  OperandIterator operands_begin() const { return NumOperandUses.begin(); }
  OperandIterator operands_end() const { return NumOperandUses.end(); }

  llvm::BasicBlock *getBasicBlock() const { return BB; }
  void add(const VectorPack *);
  void remove(const VectorPack *);
  float cost() const { return Cost; }
  const VectorPack *getProducer(llvm::Instruction *I) const {
    return InstToPackMap.lookup(I);
  }
};

#endif // end PLAN_H
