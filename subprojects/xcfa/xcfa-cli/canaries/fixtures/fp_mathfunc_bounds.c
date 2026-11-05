// Math functions such as exp are uninterpreted functions constrained by range and special-value
// facts (FpFunctionsToExprsPass). A property that follows from those facts is provable, and so is
// one that needs only functional consistency (equal arguments give equal results).
extern void abort(void);
void reach_error(){ abort(); }
extern float __VERIFIER_nondet_float(void);
extern float expf(float x);
extern float tanhf(float x);
extern float logf(float x);
extern double sin(double x);
extern float acosf(float x);
extern float atanhf(float x);

int main() {
  float x = __VERIFIER_nondet_float();
  if (x != x) return 0;
  float e = expf(x);
  if (!(e >= 0.0f)) reach_error();
  float t = tanhf(x);
  if (t > 1.0f || t < -1.0f) reach_error();
  if (x > 0.0f && t < 0.0f) reach_error();
  if (logf(1.0f) != 0.0f) reach_error();
  if (expf(0.0f) != 1.0f) reach_error();
  if (expf(x) != e) reach_error();
  double s = sin((double) x);
  if (s > 1.0 || s < -1.0) reach_error();
  if (acosf(1.0f) != 0.0f) reach_error();
  if (x >= -1.0f && x <= 1.0f && acosf(x) < 0.0f) reach_error();
  if (atanhf(1.0f) != 1.0f / 0.0f) reach_error();
  if (__builtin_signbit(-2.0) == 0 || __builtin_signbit(2.0) != 0) reach_error();
  return 0;
}
