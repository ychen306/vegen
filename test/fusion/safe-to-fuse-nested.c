// RUN: clang %s -O1 -emit-llvm -o - -c | %test-loop-fusion | FileCheck %s
// CHECK: {{[[:space:]]+}}safe
void foo(int n, int m, int x[restrict n][m], int y[restrict n][m]) {
  for (int i = 0; i < n; i++)
    for (int j = 0; j < m; j++)
      x[i][j] *= 2;

  for (int i = 0; i < n; i++)
    for (int j = 0; j < m; j++)
      y[i][j] *= 2;
}
