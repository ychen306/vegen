// RUN: clang %s -O1 -emit-llvm -o - -c | %test-loop-fusion | FileCheck %s
// CHECK: {{[[:space:]]+}}unsafe
void foo(int n, int *restrict x, int *restrict y) {
  int s = 0;
  for (int i = 0; i < n; i++)
    s += x[i];
  for (int i = 0; i < n; i++)
    y[i] *= s;
}
