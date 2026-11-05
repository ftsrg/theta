// Transcendental functions are havoced and constrained by range and special-value facts
// (FpFunctionsToExprsPass). A property that follows from those facts alone is provable.
extern void abort(void);
void reach_error(){ abort(); }
extern float __VERIFIER_nondet_float(void);
extern float expf(float x);
extern float tanhf(float x);
extern float logf(float x);
extern double sin(double x);

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
  double s = sin((double) x);
  if (s > 1.0 || s < -1.0) reach_error();
  return 0;
}
