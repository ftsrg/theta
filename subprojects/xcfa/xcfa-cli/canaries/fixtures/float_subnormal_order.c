// Subnormals used to decode back out of their IEEE fields as if they were normals, which put every
// one of them just ABOVE the smallest normal instead of far below it: 2^-149 came back as
// 2^-126*(1+2^-23) rather than 1.4e-45. A zero exponent field means two things at once -- there is
// no implicit leading 1, and the exponent is the smallest *normal* one (1-maxExponent), not the
// -maxExponent the field literally reads as -- and the decoder honoured neither.
//
// Every comparison and every arithmetic fold on an FpLitExpr goes through that decode, so this was
// a wrong ANSWER rather than lost precision: `x < FLT_MIN` was false for every subnormal x, which
// is what made `floats-cbmc-regression/float-no-simp7` regress to a wrong verdict once literals
// became exact enough for the gradual-underflow cases to be reached at all.
//
// Everything here is a constant, deliberately: constant folding is the path that calls the decoder.
extern void abort(void);
void reach_error() { abort(); }

int main() {
  const float tiny = 0x1p-149f;  /* FLT_TRUE_MIN -- least positive subnormal */
  const float mid = 0x1p-140f;   /* a subnormal in the middle of the range   */
  const float min = 0x1p-126f;   /* FLT_MIN      -- least positive normal    */

  /* the ordering the bug inverted */
  if (!(tiny < min)) reach_error();
  if (!(mid < min)) reach_error();
  if (tiny > min) reach_error();
  if (tiny >= min) reach_error();

  /* subnormals still order among themselves, and against zero */
  if (!(tiny < mid)) reach_error();
  if (!(tiny > 0.0f)) reach_error();
  if (tiny == min) reach_error();
  if (!(tiny != min)) reach_error();

  /* doubles decode through the same routine: DBL_TRUE_MIN vs DBL_MIN */
  const double dtiny = 0x1p-1074;
  const double dmin = 0x1p-1022;
  if (!(dtiny < dmin)) reach_error();
  if (!(dtiny > 0.0)) reach_error();

  /* normals must be unaffected -- the fix keys off a zero exponent field only */
  const float a = 0x1p-100f;
  const float b = 0x1p-50f;
  if (!(a < b)) reach_error();
  if (!(1.5f > 1.0f)) reach_error();

  return 0;
}
