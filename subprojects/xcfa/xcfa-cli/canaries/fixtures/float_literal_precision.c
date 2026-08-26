// Floating-point literals were built with `BinaryMathContext(significand - 1, exponent)` -- 23 bits
// for float, 52 for double -- and then stored in a full-width FpType. MPFR's precision counts the
// significand *including* the implicit leading bit (24 / 53), which is what FpUtils and FpType are
// given everywhere else, so every literal was rounded one bit short.
//
// The visible effect: 1 + 2^-23 is a tie at 23-bit precision and rounds to exactly 1.0f, so a
// program's own `1.0000001f > 1.0f` read as FALSE and safe float programs were reported Unsafe.
// Verified against gcc: all of the comparisons below are true, and 1.0000001f has exactly the bits
// 0x1.000002p+0.
//
// Both spellings are checked on purpose. The decimal one is what proves this is not about hex
// literal parsing -- it was the control that ruled that out during diagnosis.
extern void abort(void);
void reach_error(){ abort(); }

int main() {
  /* one ulp above 1.0f, written in hex and in decimal -- the same value */
  if (!(0x1.000002p+0f > 1.0f)) reach_error();
  if (!(1.0000001f > 1.0f)) reach_error();
  if (!(1.0000001f == 0x1.000002p+0f)) reach_error();

  /* the rounding that produces it: 0.75 ulp rounds up */
  float f1 = 0x1.0p+0;
  float f2 = 0x1.8p-24;
  if (!((float)(f1 + f2) == 0x1.000002p+0f)) reach_error();

  /* double keeps its full 53 bits too: 1 + 2^-52 is distinct from 1.0 */
  if (!(1.0000000000000002 > 1.0)) reach_error();

  /* values that were already exact must not change */
  if (!(0x1.8p+1 == 3.0)) reach_error();
  if (!(0x1.8p-24f > 0.0f)) reach_error();

  return 0;
}
