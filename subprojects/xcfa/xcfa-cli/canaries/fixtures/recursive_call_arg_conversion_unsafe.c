// A call that is not inlined (here: recursive) still converts its argument to the parameter type.
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "recursive_call_arg_conversion_unsafe.c", 4, "reach_error"); }
extern unsigned char __VERIFIER_nondet_uchar(void);
void g(unsigned char c, int d) {
  if (d > 0) { g(c, d - 1); return; }
  if (c != 5) reach_error();
}
int main() {
  unsigned char x = __VERIFIER_nondet_uchar();
  if (x != 5) return 0;
  g((int)x, 1);
  g(262, 1);
  return 0;
}
