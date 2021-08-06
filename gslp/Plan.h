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
  float Cost;

  llvm::DenseSet<const VectorPack *> Packs;
  struct VectorPackSlot {
    const VectorPack *VP;
    unsigned i;
  };
  // mapping inst -> the pack that contains the inst
  llvm::DenseMap<llvm::Instruction *, VectorPackSlot> InstToPackMap;
  using OperandPackSet = llvm::SmallPtrSet<const OperandPack *, 2>;
  // mapping inst -> operands that contains the instruction
  llvm::DenseMap<llvm::Instruction *, OperandPackSet> InstToOperandsMap;
  llvm::DenseMap<llvm::ArrayRef<llvm::Value *>, const VectorPack *>
      ValuesToPackMap;
  // Num scalar + vector uses
  llvm::DenseMap<const OperandPack *, int> NumVectorUses;
  llvm::DenseMap<llvm::Instruction *, int> NumScalarUses;
  llvm::DenseMap<const OperandPack *, float> ShuffleCosts;
  llvm::DenseMap<llvm::Instruction *, float> ExtractCosts;

  float computeShuffleCost(const OperandPack *) const;

  bool isAlive(llvm::Instruction *I) const;
  void kill(llvm::Instruction *);
  void revive(llvm::Instruction *);

  void incVectorUses(const OperandPack *);
  void decVectorUses(const OperandPack *);

  void decScalarUses(llvm::Instruction *);
  void incScalarUses(llvm::Instruction *);

  void updateCostOfVectorUses(llvm::ArrayRef<llvm::Value *>);

public:
  Plan() = delete;
  Plan(Packer *);
  Plan(const Plan &) = default;
  Plan(Plan &&) = default;
  Plan &operator=(const Plan &) = default;

  using PackIterator = decltype(Packs)::const_iterator;
  PackIterator begin() const { return Packs.begin(); }
  PackIterator end() const { return Packs.end(); }

  using OperandIterator = decltype(NumVectorUses)::const_iterator;
  OperandIterator operands_begin() const { return NumVectorUses.begin(); }
  OperandIterator operands_end() const { return NumVectorUses.end(); }

  void add(const VectorPack *);
  void remove(const VectorPack *);
  float cost() const { return Cost; }
  bool verifyCost() const;
  const VectorPack *getProducer(llvm::Instruction *I) const {
    auto It = InstToPackMap.find(I);
    if (It != InstToPackMap.end())
      return It->second.VP;
    return nullptr;
  }
};

#endif // end PLAN_H
