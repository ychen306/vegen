#ifndef INST_SEMA_H
#define INST_SEMA_H

#include "llvm/IR/Value.h"
#include "llvm/ADT/APInt.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/FormatVariadic.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include <vector>

struct InstSignature {
  std::vector<unsigned> InputBitwidths;
  std::vector<unsigned> OutputBitwidths;
  bool HasImm8;
  unsigned numOutputs() { return OutputBitwidths.size(); }
};

struct InputSlice {
  unsigned InputId;
  unsigned Lo, Hi;

  unsigned size() { return Hi - Lo; }

  bool operator<(InputSlice &Other) const {
    return std::tie(InputId, Lo, Hi)
      < std::tie(Other.InputId, Other.Lo, Other.Hi);
  }
};

// Interface that abstractly defines an operation
struct Operation {
  typedef std::vector<const llvm::Value *> Match;
  virtual bool numLiveins() const = 0;
  // `match' returns true if `V` is matched.
  // If a match is found, additionally return the matched liveins
  virtual bool match(const llvm::Value *V, std::vector<Match> &Matches) const = 0;
};

// An operation explicitly bound to an instruction and its input(s)
class BoundOperation {
  const Operation *Op;
  std::vector<InputSlice> BoundSlices;

public:
  // A bound operation
  BoundOperation(const Operation *Op, std::vector<InputSlice> BoundSlices)
      : Op(Op), BoundSlices(BoundSlices) {}
  const Operation *getOperation() const { return Op; }
};

class IntrinsicBuilder {
  llvm::IRBuilder<> Builder;
  llvm::Module &InstWrappers;
public:
  using InsertPoint = llvm::IRBuilderBase::InsertPoint;
  IntrinsicBuilder(InsertPoint IP, llvm::Module &InstWrappers)
  : Builder(InstWrappers.getContext()), InstWrappers(InstWrappers) {
    assert(&IP.getBlock()->getContext() == &InstWrappers.getContext());
    setInsertPoint(IP);
  }

  void setInsertPoint(InsertPoint IP) {
    Builder.SetInsertPoint(IP.getBlock(), IP.getPoint());
  }

  llvm::Value *Create(
      llvm::StringRef Name,
      llvm::ArrayRef<llvm::Value *> Operands,
      unsigned char Imm8=0) {
    using namespace llvm;
    std::string WrapperName = formatv("intrinsic_wrapper_{0}_{1}", Name, Imm8).str();
    auto *F = InstWrappers.getFunction(WrapperName);
    assert(F && "Intrinsic wrapper undefined.");

    assert(std::distance(F->begin(), F->end()) == 1 &&
        "Intrinsic Wrapper should have a single basic block");
    auto &BB = *F->begin();

    unsigned NumArgs = std::distance(F->arg_begin(), F->arg_end());
    assert(Operands.size() == NumArgs);

    // map wrapper arg to operands
    ValueToValueMapTy VMap;
    for (unsigned i = 0; i < NumArgs; i++) {
      Value *Arg = F->getArg(i);
      assert(
          CastInst::castIsValid(
            Instruction::CastOps::BitCast, Operands[i], Arg->getType()) &&
          "Invalid input type");
      Value *Operand = Builder.CreateBitCast(Operands[i], Arg->getType());
      VMap[Arg] = Operand;
    }

    Value *RetVal = nullptr;
    for (auto &I : BB) {
      if (auto *Ret = dyn_cast<ReturnInst>(&I)) {
        RetVal = Ret->getReturnValue();
        break;
      }
      auto *NewI = I.clone();
      Builder.Insert(NewI);
      VMap[&I] = NewI;
      RemapInstruction(NewI, VMap, 
          RF_NoModuleLevelChanges | RF_IgnoreMissingLocals);
    }
    assert(RetVal && "Wrapper not returning explicitly");
    Value *Output = VMap.lookup(RetVal);
    assert(Output);

    return Output;
  }
};

// An instruction is a list of lanes,
// each of which characterized by a BoundOperation
class InstBinding {
  InstSignature Sig;
  std::vector<BoundOperation> LaneOps;
  std::string Name;
  
public:
  std::string getName() { return Name; }
  InstBinding(std::string Name, InstSignature Sig, std::vector<BoundOperation> LaneOps) 
    : Name(Name), Sig(Sig), LaneOps(LaneOps) {}
  llvm::ArrayRef<BoundOperation> getLaneOps() const { return LaneOps; }
};

// this one pulls all operation that we are interested in 
// and tries to match all of them while trying to avoid
// matching the same operation twice on the same value
class MatchManager {
  // record matches for each operation
  llvm::DenseMap<const Operation *, std::vector<Operation::Match>> Matches;

public:
  MatchManager(llvm::ArrayRef<InstBinding> Insts) {
    for (auto &Inst : Insts)
      for (auto &LaneOp : Inst.getLaneOps())
        Matches.FindAndConstruct(LaneOp.getOperation());
  }

  void match(const llvm::Value *V) {
    for (auto &KV : Matches) {
      const Operation *Op = KV.first;
      std::vector<Operation::Match> &Matches = KV.second;
      Op->match(V, Matches);
    }
  }

  llvm::ArrayRef<Operation::Match> getMatches(const Operation *Op) const {
    return Matches.lookup(Op);
  }
};

template <typename LHS_TY, typename RHS_TY>
llvm::PatternMatch::CmpClass_match<LHS_TY, RHS_TY, llvm::CmpInst, llvm::CmpInst::Predicate> 
m_Cmp_dont_care(llvm::CmpInst::Predicate Pred, LHS_TY LHS, RHS_TY RHS) {
  return llvm::PatternMatch::m_Cmp(Pred, LHS, RHS);
}

static bool hasBitWidth(const llvm::Value *V, unsigned BitWidth) {
  auto *Ty = V->getType();
  if (Ty->isIntegerTy())
    return Ty->getIntegerBitWidth() == BitWidth;
  if (Ty->isFloatTy())
    return BitWidth == 32;
  if (Ty->isDoubleTy())
    return BitWidth == 64;
  return false;
}

extern std::vector<InstBinding> Insts;

#endif // end INST_SEMA_H
