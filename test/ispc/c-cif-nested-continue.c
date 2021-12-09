// RUN: %clang-o3 -march=native -mllvm -filter=kernel %s -o %t && %t

__attribute__((noinline))
void kernel(int n, float *restrict RET, float *restrict aFOO) {
  for (int programIndex = 0; programIndex < n; programIndex++) {
    float a = aFOO[programIndex];
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
  float ret[n], a[n];
  for (int i = 0; i < n; i++)
    a[i] = i + 1;

  kernel(n, ret, a);

  for (int i = 0; i < n; i++) {
    if (i == 1 && ret[i] != 11)
      return 1;
    if (i != 1 && ret[i] != 1)
      return 1;
  }

  return 0;
}
