// snprintf returns at most the longest text of its format: 22 characters for either literal here.
extern int __VERIFIER_nondet_int(void);
extern int snprintf(char *s, unsigned long n, const char *format, ...);

int main() {
  char b[4];
  unsigned int uid = __VERIFIER_nondet_int();
  const char *f = __VERIFIER_nondet_int() ? "unknown uid %u" : "";
  int n = snprintf(b, 4, f, uid);
  return n + (2147483647 - 22);
}
