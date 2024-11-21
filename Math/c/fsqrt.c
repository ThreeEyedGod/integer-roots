#include <math.h>
#include <stdio.h>
#include <float.h>
#include <arm_neon.h>


extern double sqrtC(double val)
{
    //__float128 num;
    return sqrt(val);
}
extern inline double sqrt_fsqrt(double n)
{
    double result;
    __asm__(
        "fsqrt %d0, %d1"
        : "=w"(result)
        : "w"(n));
    return result;
}
long toLong(double signif, long exp)
{
    if (signif == 0.0)
        return 0L;

    long twoTo52 = 1L << (DBL_MANT_DIG - 1); // Use DBL_MANT_DIG for precision
    long bits = *(long *)&signif;            // Convert double to long by pointer casting
    bits = (bits & (twoTo52 - 1)) | twoTo52;
    long shift = exp - (DBL_MANT_DIG - 1);

    return shift >= 0 ? bits << shift : bits >> -shift;
}