// RUN: %clang-o3 -mllvm -test-codegen %s -o %t && (%t | FileCheck %s)

// CHECK: 5
// CHECK-NEXT: 5
// CHECK-NEXT: 5
// CHECK-NEXT: 5

int printf(const char *, ...);
int a[6];
int b, c, d, h;
char e;
char *g;
int strcmp();
void f(k) {
  b = a[b] ^ a[b ^ d];
  b = 5 ^ a[b ^ d];
  b = 5 ^ a[b ^ d];
  if (k)
    printf(&e);
}
int main() {
  int i, j = 0;
  if (h && strcmp(g, ""))
    j = 1;
  for (; c; c++)
    ;
  i = 0;
  for (; i < 4; i++) {
    f(j);
    if (j)
      printf("wtf");
    printf("%X\n", b);
  }
}
