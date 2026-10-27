// As ternary_overflow_guard.c, under bitvector arithmetic.
extern int __VERIFIER_nondet_int(void);

int main() {
  int x = __VERIFIER_nondet_int();
  int r = (x < 2147483647) ? ((x + 1) & 0xff) : 0;
  return r;
}
