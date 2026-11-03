// Floating-point addition is evaluated left to right: (1.0 + 1e17) + -1e17 is 0.0, not 1.0.
extern void abort(void);
extern double __VERIFIER_nondet_double(void);
void reach_error() { abort(); }
int main(void) {
  double x = __VERIFIER_nondet_double();
  if (x == 1.0) {
    double y = x + 1e17 + -1e17;
    if (y != 0.0) reach_error();
  }
  return 0;
}
