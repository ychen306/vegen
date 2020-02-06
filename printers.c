#include <immintrin.h>
#include <stdio.h>

void print__m128i(unsigned long *val) {
    printf("%lu %lu\n", val[0], val[1]);
}

void print__m256i(unsigned long *val) {
    printf("%lu %lu %lu %lu\n", val[0], val[1], val[2], val[3]);
}

#ifdef __AVX512VL__
void print__m512i(unsigned long *val) {
    printf("%lu %lu %lu %lu %lu %lu %lu %lu\n", val[0], val[1], val[2], val[3],
        val[4], val[5], val[6], val[7]);
}
#endif

void print__m128d(double *val) {
    printf("%lf %lf\n", val[0], val[1]);
}

void print__m256d(double *val) {
    printf("%lf %lf %lf %lf\n", val[0], val[1], val[2], val[3]);
}

#ifdef __AVX512VL__
void print__m512d(double *val) {
    printf("%lf %lf %lf %lf %lf %lf %lf %lf\n",
        val[0], val[1], val[2], val[3],
        val[4], val[5], val[6], val[7]
        );
}
#endif

void print__m128(float *val) {
    printf("%f %f %f %f \n", val[0], val[1], val[2], val[3]);
}

void print__m256(float *val) {
    printf("%f %f %f %f %f %f %f %f\n",
        val[0], val[1], val[2], val[3],
        val[4], val[5], val[6], val[7]
        );
}

#ifdef __AVX512VL__
void print__m512(float *val) {
    printf("%f %f %f %f %f %f %f %f %f %f %f %f %f %f %f %f\n",
        val[0], val[1], val[2], val[3],
        val[4], val[5], val[6], val[7],
        val[8], val[9], val[10], val[11],
        val[12], val[13], val[14], val[15]
        );
}
#endif
