// RUN: %clang-o3 -march=native -mllvm -filter=kernel %s -o %t && %t

__attribute__((noinline))
void kernel(int n, float *restrict RET, float *restrict aFOO, float b) {
  for (int programIndex = 0; programIndex < n; programIndex++) {
    float a = aFOO[programIndex];
    float i, j;
    for (i = 0; i < b; ++i) {
        if (a == 1.) break;
        for (j = 0; j < b; ++j) {
            if (a == 3.) break;
            ++a;
        }
    }
    RET[programIndex] = a;
  }
}

int main() {
  int n = 1030;
  float ret[n], a[n];
  for (int i = 0; i < n; i++)
    a[i] = i + 1;

  kernel(n, ret, a, 5.);

  for (int i = 0; i < n; i++) {
    if (i == 0 && ret[i] != 1)
      return 1;
    if (i == 1 && ret[i] != 3)
      return 1;
    if (i == 2 && ret[i] != 3)
      return 1;
    if (i > 2 && ret[i] != 26 + i)
      return 1;
  }
  return 0;
}
