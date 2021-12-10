// RUN: %clang-o3 -march=native -mllvm -filter=kernel %s -o %t && %t

__attribute__((noinline))
void kernel(int n, float *RET, float *restrict aFOO) {
  for (int programIndex = 0; programIndex < n; programIndex++) {
    float v = aFOO[programIndex];
    float r = 0.;
    while (v > 0.) {
      r += 1.;
      v -= .125;
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

  for (int i = 0; i < n; i++)
    if (ret[i] != 8 + 8 * i)
      return 1;
  return 0;
}
