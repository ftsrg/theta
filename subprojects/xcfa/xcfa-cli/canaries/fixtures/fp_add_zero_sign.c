// -0.0 + 0.0 is +0.0, so x + 0.0 is not x and 1.0 / y stays positive.
extern void abort(void);
extern double __VERIFIER_nondet_double(void);
void reach_error() { abort(); }
int main(void) {
  double x = __VERIFIER_nondet_double();
  if (x == 0.0) {
    double y = x + 0.0;
    if (1.0 / y < 0.0) reach_error();
  }
  return 0;
}
