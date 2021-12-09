// RUN: %clang-o3 -march=native -mllvm -filter=kernel %s -o %t && %t

__attribute__((noinline))
void kernel(int n, float *restrict RET, float *restrict aFOO, float b) {
  for (int programIndex = 0; programIndex < n; programIndex++) {
    float a = aFOO[programIndex];
    int x;
    float aa = a;
    for (x = 0; x < 99999; ++x) {
        if (x == a) break;
        ++aa;
    }
    RET[programIndex] = aa;
  }
}

int main() {
  int n = 1030;
  float ret[n], a[n];
  for (int i = 0; i < n; i++)
    a[i] = i+1;

  kernel(n, ret, a, 5.);

  for (int i = 0; i < n; i++)
    if (ret[i] != 2 + 2 * i)
      return 1;

  return 0;
}
