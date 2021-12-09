// RUN: %clang-o3 -march=native -mllvm -filter=kernel %s -o %t && %t

__attribute__((noinline))
void kernel(int n, float *restrict ret, float *restrict a) {    
  for (int i = 0; i < n; i++) {
    float x = a[i]; 
    float r = 0.;
    do { 
      r += 1.; 
      x -= .25; 
    } while (x > 0.);
    ret[i] = r;
  }
}

int main() {
  int n = 1024;
  float ret[n], a[n];
  for (int i = 0; i < n; i++)
    a[i] = i+1;

  kernel(n, ret, a);

  for (int i = 0; i < n; i++)
    if (ret[i] != 4 * (i+1)) {
      return 1;
    }
  return 0;
}
