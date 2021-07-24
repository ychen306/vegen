// RUN: clang %s -O1 -emit-llvm -o - -c | %test-loop-fusion | FileCheck %s
// CHECK: {{[[:space:]]+}}unsafe
void foo(int n, int *x, int *y) {
  for (int i = 0; i < n; i++)
    x[i] += 2;
  for (int i = 0; i < n; i++)
    // can't interleave * and + as reductions
    y[i] *= 2;
}
