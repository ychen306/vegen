// RUN: %clang-o3 -march=native -mllvm -filter=kernel %s -o %t && %t

float sqrtf(float);

__attribute__((noinline))
void kernel(int n, float *restrict RET, float *restrict aFOO) {
  for (int programIndex = 0; programIndex < n; programIndex++) {
    float a = aFOO[programIndex];
    int i, j=0;
    for (i=a; i < 10; ++i) {
        j += sqrtf((a / 3.f) * (1.f / (i+2)));
        if (i >= 5) continue;
        j += sqrtf(((a+2) / 3.f) * (1.f / (i+3)));
    }
    RET[programIndex] = (float)j; 
  }
}


int main() {
  int n = 1030;
  float ret[n], a[n];
  for (int i = 0; i < n; i++)
    a[i] = i + 1;

  kernel(n, ret, a);

  for (int i = 0; i < n; i++)
    if (ret[i] != 0)
      return 1;
  return 0;
}
