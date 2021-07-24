// RUN: clang %s -O1 -emit-llvm -o - -c | %test-loop-fusion | FileCheck %s
// CHECK: {{[[:space:]]+}}unsafe
int bar();
void foo(int n, int *restrict x, int *restrict y) {
  for (int i = 0; i < n; i++) {
    x[i] *= 2;
    bar();
  }
  for (int i = 0; i < n; i++)
    y[i] *= 2;
}
