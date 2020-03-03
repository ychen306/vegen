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
