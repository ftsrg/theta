// The glibc __fpclassify* entry points and isnormal on every class, for float, double and long
// double (binary128).
extern void abort(void);
void reach_error(){ abort(); }
extern int __fpclassify(double);
extern int __fpclassifyf(float);
extern int __fpclassifyl(long double);
extern int isnormal(double);

enum { NAN_ = 0, INF_ = 1, ZERO_ = 2, SUB_ = 3, NORM_ = 4 };

int main() {
  volatile double d = 1.0;
  float f = 1.0f;
  long double l = 1.0L;
  double dz = 0.0, dinf = 1.0e300 * 1.0e300, dnan = dinf - dinf, dsub = 4.9e-324;
  float fz = 0.0f, finf = 3.0e38f * 10.0f, fnan = finf - finf, fsub = 1.0e-45f;
  long double lz = 0.0L, linf = 1.0e4000L * 1.0e4000L, lnan = linf - linf, lsub = 1.0e-4950L;

  if (__fpclassify(dnan) != NAN_) reach_error();
  if (__fpclassify(dinf) != INF_) reach_error();
  if (__fpclassify(-dinf) != INF_) reach_error();
  if (__fpclassify(dz) != ZERO_) reach_error();
  if (__fpclassify(-dz) != ZERO_) reach_error();
  if (__fpclassify(dsub) != SUB_) reach_error();
  if (__fpclassify(d) != NORM_) reach_error();

  if (__fpclassifyf(fnan) != NAN_) reach_error();
  if (__fpclassifyf(finf) != INF_) reach_error();
  if (__fpclassifyf(fz) != ZERO_) reach_error();
  if (__fpclassifyf(fsub) != SUB_) reach_error();
  if (__fpclassifyf(f) != NORM_) reach_error();

  if (__fpclassifyl(lnan) != NAN_) reach_error();
  if (__fpclassifyl(linf) != INF_) reach_error();
  if (__fpclassifyl(lz) != ZERO_) reach_error();
  if (__fpclassifyl(lsub) != SUB_) reach_error();
  if (__fpclassifyl(l) != NORM_) reach_error();

  if (!isnormal(d)) reach_error();
  if (isnormal(dz) || isnormal(dsub) || isnormal(dinf) || isnormal(dnan))
    reach_error();
  return 0;
}
