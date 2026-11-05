// The overflow of `k + 1` does not depend on the snprintf stub, so it is still reported.
extern int __VERIFIER_nondet_int(void);
extern int snprintf(char *s, unsigned long n, const char *format, ...);

int main() {
  char b[4];
  int n = snprintf(b, 4, "%s", "ab");
  int k = __VERIFIER_nondet_int();
  int x = k + 1;
  return x - n;
}
