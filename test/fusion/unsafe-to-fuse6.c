// RUN: true
void foo(int n, int *restrict x, int *restrict y, int *t1, int *t2) {
  int s = 0;
  for (int i = 0; i < n; i++)
    s += x[i];
  *t1 = s;
  int t = *t2 ? 34 : 45; // x is potentially (control-)dependent on the first loop
  for (int i = 0; i < n; i++)
    y[i] *= t;
}
