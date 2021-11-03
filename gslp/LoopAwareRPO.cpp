#include "LoopAwareRPO.h"
#include "llvm/Analysis/LoopInfo.h"

using namespace llvm;

namespace {
class LoopAwareRPO {
  LoopInfo &LI;

  SmallPtrSet<Loop *, 8> VisitedLoops;
  DenseSet<BasicBlock *> VisitedBlocks;

  std::vector<BasicBlock *> RPO;
  SmallVector<Loop *, 8> LoopStack{nullptr};

  Loop *curLoop() const { return LoopStack.back(); }

  void visitLoop(Loop *L) {
    if (!VisitedLoops.insert(L).second)
      return;
    SmallVector<BasicBlock *, 4> Exits;
    L->getExitBlocks(Exits);
    for (auto *Exit : Exits)
      visitBlock(Exit);

    LoopStack.push_back(L);
    visitBlock(L->getHeader());
    LoopStack.pop_back();
  }

  void visitBlock(BasicBlock *BB) {
    if (!VisitedBlocks.insert(BB).second)
      return;

    assert(LI.getLoopFor(BB) == curLoop());

    for (auto *Succ : successors(BB)) {
      auto *SuccL = LI.getLoopFor(Succ);
      if (SuccL == curLoop())
        visitBlock(Succ);
      else if (!curLoop() || curLoop()->contains(Succ))
        visitLoop(SuccL);
      // otherwise Succ is an exit block,
      // which we don't deal with here (we will with that in visit Loop)
    }

    RPO.push_back(BB);
  }

public:
  using iterator = decltype(RPO)::const_iterator;
  LoopAwareRPO(Function *F, LoopInfo &LI) : LI(LI) {
    visitBlock(&F->getEntryBlock());
    std::reverse(RPO.begin(), RPO.end());
  }

  iterator begin() const { return RPO.begin(); }
  iterator end() const { return RPO.end(); }
};

} // namespace

void computeRPO(Function *F, LoopInfo &LI, SmallVectorImpl<BasicBlock *> &Blocks) {
  LoopAwareRPO RPO(F, LI);
  Blocks.clear();
  Blocks.append(RPO.begin(), RPO.end());
}
