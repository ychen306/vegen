// RUN: %clang-o3 -march=native -mllvm -filter=kernel %s -o %t && %t

__attribute__((noinline))
void kernel(int n, float *RET, float *restrict aFOO) {
  for (int programIndex = 0; programIndex < n; programIndex++) {
    float a = aFOO[programIndex];
    while (a < 10)
      ++a;
    RET[programIndex] = a;
  }
}

int main() {
  int n = 1030;
  float a[n], ret[n];
  for (int i = 0; i < n; i++)
    a[i] = i+1;

  kernel(n, ret, a);

  for (int i = 0; i < n; i++) {
    float expected = 1 + i;
    if (expected < 10)
      expected = 10;
    if (ret[i] != expected)
      return 1;
  }
  return 0;
}
