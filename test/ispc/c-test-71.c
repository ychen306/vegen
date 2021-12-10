// RUN: %clang-o3 -march=native -mllvm -filter=kernel %s -o %t && %t

__attribute__((noinline))
void kernel(int n, float *restrict RET, float *restrict aFOO, float b) {
  for (int programIndex = 0; programIndex < n; programIndex++) {
    float a = aFOO[programIndex];
    float i, r = a;
    if (a >= 4) {
      RET[programIndex] = 0;
    } else {
      for (i = 0; i < a; ++i) {
        if (r == b)
          r += 10;
        ++r;
        if (r == 2) break;
      }
      RET[programIndex] = r;
    }
  }
}

int main() {
  int n = 1030;
  float ret[n], a[n];
  for (int i = 0; i < n; i++)
    a[i] = i + 1;

  kernel(n, ret, a, 5.);

  for (int i = 0; i < n; i++) {
    float expected = 0;
    if (i == 0)
      expected = 2;
    if (i == 1)
      expected = 4;
    if (i == 2)
      expected = 16;

    if (ret[i] != expected)
      return 1;
  }
  return 0;
}
