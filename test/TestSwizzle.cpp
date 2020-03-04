#include "gtest.h"
#include "ShuffleSema.h"
#include "llvm/ADT/BitVector.h"

using namespace llvm;

TEST(Swizzle, SliceIntersect) {
  SwizzleValue V(16);
  SwizzleInput X(&V);
  Slice S1(&X, 4, 8);
  Slice S2(&X, 5, 9);
  Slice S3(&X, 8, 9);
  ASSERT_TRUE(S1.intersectWith(S2));
  ASSERT_FALSE(S1.intersectWith(S3));
}

TEST(Swizzle, ParamUpdateCtr) {
  SwizzleValue V(16);
  SwizzleInput X(&V);
  ParameterUpdate U(&X, 8);
}

TEST(Swizzle, ParamUpdateCompat) {
  SwizzleValue V(16);
  SwizzleInput X(&V);
  Slice S1(&X, 4, 8);
  Slice S2(&X, 5, 9);
  Slice S3(&X, 8, 9);

  ParameterUpdate U1(&S1, 0);
  ParameterUpdate U2(&S2, 0);
  ParameterUpdate U3(&S3, 0);
  ASSERT_TRUE(U1.compatibleWith(U2));
  ASSERT_TRUE(U1.compatibleWith(U3));
  ASSERT_TRUE(U2.compatibleWith(U3));

  ParameterUpdate Ua(&S1, 0);
  ParameterUpdate Ub(&S2, 1);
  ParameterUpdate Uc(&S3, 2);
  ASSERT_FALSE(Ua.compatibleWith(Ub));
  ASSERT_TRUE(Ua.compatibleWith(Uc));
}

TEST(Swizzle, ParamMapUpdate) {
  SwizzleValue V(16);
  SwizzleInput X(&V); 

  BitVector Target(16);
  Target.set(0);
  Target.set(1);
  Target.set(4);
  Target.set(10);

  Slice S1(&X, 0, 2); // set bit 0 and 1
  ParameterUpdate U1(&S1, 0b11);
  Slice S2(&X, 3, 5); // set bit 4
  ParameterUpdate U2(&S2, 0b10);
  Slice S3(&X, 8, 12); // set bit 10
  ParameterUpdate U3(&S3, 0b100);

  ParameterMap PM({ &V });
  PM.update(U1);
  PM.update(U2);
  PM.update(U3);
  ASSERT_EQ(Target, PM.get(&V));
  PM.update(ParameterUpdate(&S3, 0b110));
  ASSERT_NE(Target, PM.get(&V));
}

namespace {

// auxiliary environment with llvm types and constants we need for testing
struct AuxEnv {
  LLVMContext Ctx;
  std::vector<Constant *> I8Values;
  std::vector<Constant *> I32Values;
  IntegerType *I8, *I32;

  AuxEnv(unsigned NumValues=256) {
    I8 = Type::getInt8Ty(Ctx);
    I32 = Type::getInt32Ty(Ctx);

    for (unsigned i = 0; i < NumValues; i++) {
      I8Values.push_back(ConstantInt::get(I8, i));
      I32Values.push_back(ConstantInt::get(I32, i));
    }
  }

  std::vector<Constant *> selectValues(ArrayRef<Constant *> Values, std::vector<unsigned> Idxs) const {
    std::vector<Constant *> Selected;
    for (unsigned i : Idxs)
      Selected.push_back(Values[i]);
    return Selected;
  }
} Aux;

Swizzle buildDummySwizzleKernel(
    std::vector<const SwizzleValue *> Inputs,
    std::vector<const SwizzleValue *> Outputs,
    std::vector<const SwizzleOp *> OutputSema) {
  InstSignature Sig;
  Sig.InputBitwidths.resize(Inputs.size());
  Sig.OutputBitwidths.resize(Outputs.size());
  std::vector<AbstractSwizzleOutput> AbstractOutputs;
  for (auto *X : Outputs) {
    AbstractOutputs.push_back(AbstractSwizzleOutput(1,0,{}));
  }
  Swizzle Kernel(
      Sig, OutputSema, Inputs, Outputs, AbstractOutputs);
  return Kernel;
}

std::vector<Value *> toValueVector(const std::vector<Constant *> &Constants) {
  std::vector<Value *> Values;
  for (auto *C : Constants)
    Values.push_back(C);
  return Values;
}

VectorPack createInputPack(unsigned BitWidth, std::vector<Constant *> X) {
  return VectorPack(BitWidth, toValueVector(X), ConstantVector::get(X));
}

VectorPack createOutputPack(unsigned BitWidth, std::vector<Constant *> X) {
  return VectorPack(BitWidth, toValueVector(X));
}

} // end anonymous namespace

TEST(Swizzle, ParamSolvingSimple) {
  // basic kernel: 1234 -> 1234
  VectorPack X = createInputPack(8, Aux.selectValues(Aux.I8Values, {0,1,2,3}));
  VectorPack Y = createInputPack(8, Aux.selectValues(Aux.I8Values, {0,1,2,3}));
  VectorPack Y2 = createOutputPack(8, Aux.selectValues(Aux.I8Values, {0,1,3,2}));

  unsigned BW = 4 * 8;
  SwizzleValue Sx(BW);
  SwizzleValue Sy(BW);
  SwizzleInput Sema(&Sx);

  Swizzle Kernel = buildDummySwizzleKernel({&Sx}, {&Sy}, {&Sema});
  SwizzleEnv Env;
  OrderedInstructions *OI = nullptr;
  ASSERT_TRUE(Kernel.solve({{X}, {Y}}, Env, OI));
  ASSERT_FALSE(Kernel.solve({{X}, {Y2}}, Env, OI));
  ASSERT_EQ(Env[&Sx], X.getPackedContent());
}

TEST(Swizzle, ParamSolvingUnpackLo) {
  // unpack lo : 0123 x 4567 -> 0426
  VectorPack X1 = createInputPack(8, Aux.selectValues(Aux.I8Values, {0,1,2,3}));
  VectorPack X2 = createInputPack(8, Aux.selectValues(Aux.I8Values, {4,5,6,7}));
  VectorPack Y = createOutputPack(8, Aux.selectValues(Aux.I8Values, {0,4,2,6}));

  unsigned BW = 4 * 8;
  SwizzleValue Sx1(BW);
  SwizzleValue Sx2(BW);
  SwizzleValue Sy(BW);

  SwizzleInput Input1(&Sx1);
  SwizzleInput Input2(&Sx2);
  Slice Lane1(&Input1, 0, 8);
  Slice Lane2(&Input2, 0, 8);
  Slice Lane3(&Input1, 16, 24);
  Slice Lane4(&Input2, 16, 24);
  Concat Sema({&Lane1, &Lane2, &Lane3, &Lane4});

  Swizzle Kernel = buildDummySwizzleKernel({&Sx1, &Sx2}, {&Sy}, {&Sema});
  SwizzleEnv Env;
  OrderedInstructions *OI = nullptr;
  ASSERT_TRUE(Kernel.solve({{X1, X2}, {Y}}, Env, OI));
  ASSERT_EQ(Env[&Sx1], X1.getPackedContent());
  ASSERT_EQ(Env[&Sx2], X2.getPackedContent());
}
