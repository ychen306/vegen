#include "BlockBuilder.h"
#include "ControlDependence.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/CommandLine.h"

using namespace llvm;

static cl::opt<bool> RunTest1("test1", cl::init(false));
static cl::opt<bool> RunTest2("test2", cl::init(false));
static cl::opt<bool> RunTest3("test3", cl::init(false));

static void test1() {
  LLVMContext Ctx;
  auto *Int1Ty = Type::getInt1Ty(Ctx);
  auto *FTy = FunctionType::get(Type::getVoidTy(Ctx), {Int1Ty, Int1Ty, Int1Ty},
                                false /*var args*/);
  auto *F =
      Function::Create(FTy, GlobalValue::LinkageTypes::InternalLinkage, "foo");

  BlockBuilder Builder(BasicBlock::Create(Ctx, "entry", F), [](Value *V) { return V; });
  DominatorTree DT(*F);
  PostDominatorTree PDT(*F);
  LoopInfo LI(DT);
  ControlDependenceAnalysis CDA(LI, DT, PDT);

  const ControlCondition *True = nullptr;
  auto *X1 = F->getArg(0);
  auto *X2 = F->getArg(1);
  auto *X3 = F->getArg(2);
  X1->setName("x1");
  X2->setName("x2");
  X3->setName("x3");

  auto *C12 = CDA.getAnd(CDA.getAnd(True, X1, true), X2, true);
  auto *C13 = CDA.getAnd(CDA.getAnd(True, X1, true), X3, true);
  auto *C = CDA.getOr({C12, C13});

  BinaryOperator::CreateNot(X1, "DUMMY", Builder.getBlockFor(C));
  ReturnInst::Create(Ctx, Builder.getBlockFor(nullptr));

  outs() << *F << '\n';
  delete F;
}

static void test2() {
  LLVMContext Ctx;
  auto *Int1Ty = Type::getInt1Ty(Ctx);
  auto *FTy = FunctionType::get(Type::getVoidTy(Ctx), {Int1Ty, Int1Ty, Int1Ty},
                                false /*var args*/);
  auto *F =
      Function::Create(FTy, GlobalValue::LinkageTypes::InternalLinkage, "foo");

  BlockBuilder Builder(BasicBlock::Create(Ctx, "entry", F), [](Value *V) { return V; });
  DominatorTree DT(*F);
  PostDominatorTree PDT(*F);
  LoopInfo LI(DT);
  ControlDependenceAnalysis CDA(LI, DT, PDT);

  const ControlCondition *True = nullptr;
  auto *X1 = F->getArg(0);
  auto *X2 = F->getArg(1);
  auto *X3 = F->getArg(2);
  X1->setName("x1");
  X2->setName("x2");
  X3->setName("x3");

  auto *C1 = CDA.getAnd(True, X1, true);
  auto *C2 = CDA.getAnd(True, X2, true);
  auto *C = CDA.getOr({C1, C2});

  BinaryOperator::CreateNot(X1, "DUMMY", Builder.getBlockFor(C));
  ReturnInst::Create(Ctx, Builder.getBlockFor(nullptr));

  outs() << *F << '\n';
  delete F;
}

static void test3() {
  LLVMContext Ctx;
  auto *Int1Ty = Type::getInt1Ty(Ctx);
  auto *FTy = FunctionType::get(Type::getVoidTy(Ctx), {Int1Ty, Int1Ty, Int1Ty},
                                false /*var args*/);
  auto *F =
      Function::Create(FTy, GlobalValue::LinkageTypes::InternalLinkage, "foo");

  BlockBuilder Builder(BasicBlock::Create(Ctx, "entry", F), [](Value *V) { return V; });
  DominatorTree DT(*F);
  PostDominatorTree PDT(*F);
  LoopInfo LI(DT);
  ControlDependenceAnalysis CDA(LI, DT, PDT);

  const ControlCondition *True = nullptr;
  auto *X1 = F->getArg(0);
  auto *X2 = F->getArg(1);
  auto *X3 = F->getArg(2);
  X1->setName("x1");
  X2->setName("x2");
  X3->setName("x3");

  auto *If_X1 = CDA.getAnd(True, X1, true);
  BinaryOperator::CreateNot(X1, "DUMMY-if-x1", Builder.getBlockFor(If_X1));

  auto *If_X2 = CDA.getAnd(True, X2, true);
  auto *Or_X1_X2 = CDA.getOr({If_X1, If_X2});
  BinaryOperator::CreateNot(X1, "DUMMY-x1-or-x2", Builder.getBlockFor(Or_X1_X2));

  ReturnInst::Create(Ctx, Builder.getBlockFor(nullptr));

  outs() << *F << '\n';
  delete F;
}

int main(int argc, char **argv) {
  cl::ParseCommandLineOptions(argc, argv);

  if (RunTest1)
    test1();
  if (RunTest2)
    test2();
  if (RunTest3)
    test3();
  return 0;
}
