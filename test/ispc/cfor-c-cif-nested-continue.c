// RUN: %clang-o3 -march=native -mllvm -filter=kernel %s -o %t && %t

__attribute__((noinline))
void kernel(int n, float *RET, float *restrict aFOO) {
  for (int programIndex = 0; programIndex < n; programIndex++) {
    float a = aFOO[programIndex&0x3];
    int i, j;
    float r = 0;
    for (i = 0; i < a; ++i) {
      if (i != 0) {
        if (a != 2)
          continue;
        r = 10;
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
    float expected = 1;
    if (i % 4 == 1)
      expected = 11;
    if (ret[i] != expected)
      return 1;
  }
  return 0;
}
