// memcpy with a symbolic byte count is lowered to a loop over n/sizeof elements.
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "memcpy_symbolic.c", 3, "reach_error"); }
extern void *memcpy(void *, const void *, unsigned long);
extern int __VERIFIER_nondet_int(void);
int main() {
  char a[10], b[10];
  int n = __VERIFIER_nondet_int();
  if (n < 0 || n > 10) return 0;
  a[0] = 1;
  b[0] = 2;
  memcpy(b, a, n);
  if (n > 0 && b[0] != 1) reach_error();
  if (n == 0 && b[0] != 2) reach_error();
  return 0;
}
