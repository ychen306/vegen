// RUN: clang %s -O1 -emit-llvm -o - -c | %test-loop-fusion | FileCheck %s
// CHECK: {{[[:space:]]+}}safe
void foo(int n, int *restrict x, int *restrict y) {
  for (int i = 0; i < n; i++)
    x[i] *= 2;
  for (int i = 0; i < n; i++)
    y[i] *= 2;
}
