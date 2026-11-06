// The format is one of two literals: "unknown uid %u" gives at most 22 characters, "" none.
extern int __VERIFIER_nondet_int(void);
extern int snprintf(char *s, unsigned long n, const char *format, ...);

int main() {
  char b[4];
  unsigned int uid = __VERIFIER_nondet_int();
  const char *f = __VERIFIER_nondet_int() ? "unknown uid %u" : "";
  int n = snprintf(b, 4, f, uid);
  return n + 1;
}
