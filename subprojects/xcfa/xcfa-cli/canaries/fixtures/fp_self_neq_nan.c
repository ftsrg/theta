// x != x holds exactly when x is NaN, so the error is reachable.
extern void abort(void);
extern double __VERIFIER_nondet_double(void);
void reach_error() { abort(); }
int main(void) {
  double x = __VERIFIER_nondet_double();
  if (x != x) reach_error();
  return 0;
}
