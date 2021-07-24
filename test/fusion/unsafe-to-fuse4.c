// RUN: clang %s -O1 -emit-llvm -o - -c | %test-loop-fusion | FileCheck %s
// CHECK: {{[[:space:]]+}}unsafe
void foo(int n, int *x, int *y) {
  if (n % 2)
    for (int i = 0; i < n; i++)
      x[i] += 2;
  if (n % 3)
    for (int i = 0; i < n; i++)
      y[i] += 2;
}
