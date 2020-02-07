#include <immintrin.h>

void print__m128i(unsigned long *val);
void print__m256i(unsigned long *val);

#ifdef __AVX512VL__
void print__m512i(unsigned long *val);
#endif

void print__m128d(double *val);
void print__m256d(double *val);

#ifdef __AVX512VL__
void print__m512d(double *val);
#endif

void print__m128(float *val);

void print__m256(float *val);

#ifdef __AVX512VL__
void print__m512(float *val);
#endif
