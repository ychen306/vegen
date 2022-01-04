// RUN: %clang-o3 %s -o /dev/null -c
void s482(int n, float *restrict a, float *restrict b, float *restrict c) {
  for (int i = 0; i < n; i++) {
    a[i] += b[i] * c[i];
    if (c[i] > b[i])
      break;
  }
}
