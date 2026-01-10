/*
 *  Copyright 2025 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.frontend.stdlib

internal val math_h =
  """
extern double acos(double x);
extern float acosf(float x);
extern long double acosl(long double x);
extern double asin(double x);
extern float asinf(float x);
extern long double asinl(long double x);
extern double atan(double x);
extern float atanf(float x);
extern long double atanl(long double x);
extern double atan2(double y, double x);
extern float atan2f(float y, float x);
extern long double atan2l(long double y, long double x);
extern double cos(double x);
extern float cosf(float x);
extern long double cosl(long double x);
extern double sin(double x);
extern float sinf(float x);
extern long double sinl(long double x);
extern double tan(double x);
extern float tanf(float x);
extern long double tanl(long double x);
extern double acosh(double x);
extern float acoshf(float x);
extern long double acoshl(long double x);
extern double asinh(double x);
extern float asinhf(float x);
extern long double asinhl(long double x);
extern double atanh(double x);
extern float atanhf(float x);
extern long double atanhl(long double x);
extern double cosh(double x);
extern float coshf(float x);
extern long double coshl(long double x);
extern double sinh(double x);
extern float sinhf(float x);
extern long double sinhl(long double x);
extern double tanh(double x);
extern float tanhf(float x);
extern long double tanhl(long double x);
extern double exp(double x);
extern float expf(float x);
extern long double expl(long double x);
extern double exp2(double x);
extern float exp2f(float x);
extern long double exp2l(long double x);
extern double expm1(double x);
extern float expm1f(float x);
extern long double expm1l(long double x);
extern double frexp(double value, int *exp);
extern float frexpf(float value, int *exp);
extern long double frexpl(long double value, int *exp);
extern int ilogb(double x);
extern int ilogbf(float x);
extern int ilogbl(long double x);
extern double ldexp(double x, int exp);
extern float ldexpf(float x, int exp);
extern long double ldexpl(long double x, int exp);
extern double log(double x);
extern float logf(float x);
extern long double logl(long double x);
extern double log10(double x);
extern float log10f(float x);
extern long double log10l(long double x);
extern double log1p(double x);
extern float log1pf(float x);
extern long double log1pl(long double x);
extern double log2(double x);
extern float log2f(float x);
extern long double log2l(long double x);
extern double logb(double x);
extern float logbf(float x);
extern long double logbl(long double x);
extern double modf(double value, double *iptr);
extern float modff(float value, float *iptr);
extern long double modfl(long double value, long double *iptr);
extern double scalbn(double x, int n);
extern float scalbnf(float x, int n);
extern long double scalbnl(long double x, int n);
extern double scalbln(double x, long int n);
extern float scalblnf(float x, long int n);
extern long double scalblnl(long double x, long int n);
extern double cbrt(double x);
extern float cbrtf(float x);
extern long double cbrtl(long double x);
extern double fabs(double x);
extern float fabsf(float x);
extern long double fabsl(long double x);
extern double hypot(double x, double y);
extern float hypotf(float x, float y);
extern long double hypotl(long double x, long double y);
extern double pow(double x, double y);
extern float powf(float x, float y);
extern long double powl(long double x, long double y);
extern double sqrt(double x);
extern float sqrtf(float x);
extern long double sqrtl(long double x);
extern double erf(double x);
extern float erff(float x);
extern long double erfl(long double x);
extern double erfc(double x);
extern float erfcf(float x);
extern long double erfcl(long double x);
extern double lgamma(double x);
extern float lgammaf(float x);
extern long double lgammal(long double x);
extern double tgamma(double x);
extern float tgammaf(float x);
extern long double tgammal(long double x);
extern double ceil(double x);
extern float ceilf(float x);
extern long double ceill(long double x);
extern double floor(double x);
extern float floorf(float x);
extern long double floorl(long double x);
extern double nearbyint(double x);
extern float nearbyintf(float x);
extern long double nearbyintl(long double x);
extern double rint(double x);
extern float rintf(float x);
extern long double rintl(long double x);
extern long int lrint(double x);
extern long int lrintf(float x);
extern long int lrintl(long double x);
extern long long int llrint(double x);
extern long long int llrintf(float x);
extern long long int llrintl(long double x);
extern double round(double x);
extern float roundf(float x);
extern long double roundl(long double x);
extern long int lround(double x);
extern long int lroundf(float x);
extern long int lroundl(long double x);
extern long long int llround(double x);
extern long long int llroundf(float x);
extern long long int llroundl(long double x);
extern double trunc(double x);
extern float truncf(float x);
extern long double truncl(long double x);
extern double fmod(double x, double y);
extern float fmodf(float x, float y);
extern long double fmodl(long double x, long double y);
extern double remainder(double x, double y);
extern float remainderf(float x, float y);
extern long double remainderl(long double x, long double y);
extern double remquo(double x, double y, int *quo);
extern float remquof(float x, float y, int *quo);
extern long double remquol(long double x, long double y, int *quo);
extern double copysign(double x, double y);
extern float copysignf(float x, float y);
extern long double copysignl(long double x, long double y);
extern double nan(const char *tagp);
extern float nanf(const char *tagp);
extern long double nanl(const char *tagp);
extern double nextafter(double x, double y);
extern float nextafterf(float x, float y);
extern long double nextafterl(long double x, long double y);
extern double nexttoward(double x, long double y);
extern float nexttowardf(float x, long double y);
extern long double nexttowardl(long double x, long double y);
extern double fdim(double x, double y);
extern float fdimf(float x, float y);
extern long double fdiml(long double x, long double y);
extern double fmax(double x, double y);
extern float fmaxf(float x, float y);
extern long double fmaxl(long double x, long double y);
extern double fmin(double x, double y);
extern float fminf(float x, float y);
extern long double fminl(long double x, long double y);
extern double fma(double x, double y, double z);
extern float fmaf(float x, float y, float z);
extern long double fmal(long double x, long double y, long double z);
"""
    .trimIndent()
