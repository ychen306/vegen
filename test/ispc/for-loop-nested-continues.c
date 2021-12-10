// RUN: %clang-o3 -march=native -mllvm -filter=kernel %s -o %t && %t

__attribute__((noinline))
void kernel(int n, float *RET, float *restrict aFOO) {
  for (int programIndex = 0; programIndex < n; programIndex++) {
    float a = aFOO[programIndex];
    int i, j;
    float r = 0;
    for (i = 0; i < a+1; ++i) {
      if (i == 1)
        continue;
      for (j = 0; j < a; ++j) {
        if (a == 2)
          continue;
      }
      ++r;
    }
    RET[programIndex] = r;
  }
}

int main() {
  int n = 1030;
  float a[n], ret[n];
  for (int i = 0; i < n; i++)
    a[i] = i+1;

  kernel(n, ret, a);

  for (int i = 0; i < n; i++) {
    if (ret[i] != i + 1)
      return 1;
  }
  return 0;
}
