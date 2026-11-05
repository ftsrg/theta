extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "nan-return.c", 2, "reach_error"); }
extern float __VERIFIER_nondet_float(void);
int main(void) {
  float x = __VERIFIER_nondet_float();
  if (x != x) { reach_error(); }
  return 0;
}
