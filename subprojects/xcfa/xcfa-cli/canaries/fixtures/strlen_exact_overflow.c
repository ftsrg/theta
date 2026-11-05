// strlen is exact and not over-approximated: with 10 characters the sum overflows.
extern char __VERIFIER_nondet_char(void);
extern unsigned long strlen(const char *s);

int main() {
  char a[11];
  for (int i = 0; i < 10; ++i) a[i] = __VERIFIER_nondet_char();
  a[10] = 0;
  int n = (int)strlen(a);
  return n + (2147483647 - 9);
}
