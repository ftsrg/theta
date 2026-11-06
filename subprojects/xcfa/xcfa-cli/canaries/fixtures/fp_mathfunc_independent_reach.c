// The error path runs through sinf but does not use its result, so the over-approximated value
// cannot make the counterexample spurious: it is still reported.
extern void abort(void);
void reach_error() { abort(); }
extern int __VERIFIER_nondet_int(void);
extern float sinf(float x);

int main() {
  float s = sinf(1.0f);
  int k = __VERIFIER_nondet_int();
  if (k == 7) reach_error();
  return s > 2.0f;
}
