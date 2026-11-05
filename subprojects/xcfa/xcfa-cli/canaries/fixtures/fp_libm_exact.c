// nan, fdim, remainder and modf have exact FP-theory models (FpFunctionsToExprsPass); before
// those, each call failed the analysis as "No such method".
//
// remainder rounds the quotient to nearest-even (7/2 = 3.5 -> 4, so the result is -1), which is
// what tells it apart from fmod. modf must give the fraction the sign of x: -3.0 - trunc(-3.0)
// alone would be +0.0, and 1/(+0.0) is +inf.
extern void abort(void);
void reach_error(){ abort(); }
extern float nanf(const char *tagp);
extern double nan(const char *tagp);
extern float fdimf(float x, float y);
extern double remainder(double x, double y);
extern float remainderf(float x, float y);
extern float modff(float x, float *iptr);

int main() {
  float n = nanf("");
  if (n == n) reach_error();
  double dn = nan("");
  if (dn == dn) reach_error();

  if (fdimf(5.0f, 3.0f) != 2.0f) reach_error();
  if (fdimf(3.0f, 5.0f) != 0.0f) reach_error();
  if (1.0f / fdimf(3.0f, 5.0f) < 0.0f) reach_error();
  float fd = fdimf(n, 1.0f);
  if (fd == fd) reach_error();

  if (remainder(7.0, 2.0) != -1.0) reach_error();
  if (remainder(5.0, 2.0) != 1.0) reach_error();
  if (remainderf(-7.5f, 2.0f) != 0.5f) reach_error();

  float ip;
  float fr = modff(-3.25f, &ip);
  if (ip != -3.0f || fr != -0.25f) reach_error();
  fr = modff(-3.0f, &ip);
  if (1.0f / fr > 0.0f) reach_error();
  fr = modff(1.0f / 0.0f, &ip);
  if (fr != 0.0f || ip != 1.0f / 0.0f) reach_error();
  return 0;
}
