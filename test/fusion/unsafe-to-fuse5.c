// RUN: clang %s -O1 -emit-llvm -o - -c | %test-loop-fusion | FileCheck %s
// CHECK: {{[[:space:]]+}}unsafe
void foo(int n, int *restrict x, int *restrict y, int *t1, int *t2) {
  int s = 0;
  for (int i = 0; i < n; i++)
    s += x[i];
  *t1 = s;
  for (int i = 0; i < n; i++)
    y[i] *= *t2;
}
