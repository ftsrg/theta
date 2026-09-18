// theta models exactly one rounding mode -- round-to-nearest-even, the C default. `fesetround` was
// silently ignored, so a program that selects FE_DOWNWARD went on being evaluated round-to-nearest
// and the verdict came out confidently wrong: floats-cbmc-regression/float-rounding1 asserts a sum
// under downward rounding and was reported Unsafe although it is safe.
//
// An honest refusal scores 0; a wrong answer scores -16. So a non-default mode is refused. A
// non-constant argument is refused too -- it cannot be shown to be the default.
extern int fesetround(int);
int main() {
  fesetround(0x400);            /* FE_DOWNWARD */
  float a = 1.0f, b = 0x1.8p-24;
  return (float)(a + b) == 1.0f;
}
