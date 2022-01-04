// RUN: %clang-o3 %s -o /dev/null -c

#define LEN2 256

float aa[LEN2][LEN2], bb[LEN2][LEN2], cc[LEN2][LEN2];

void s275() {
  for (int i = 0; i < LEN2; i++) {
    if (aa[0][i] > (float)0.) {
      for (int j = 1; j < LEN2; j++) {
        aa[j][i] = aa[j - 1][i] + bb[j][i] * cc[j][i];
      }
    }
  }
}
