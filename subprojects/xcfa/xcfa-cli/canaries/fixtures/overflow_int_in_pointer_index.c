// The `int` sum inside a pointer offset is signed arithmetic, so its overflow is still reported.
extern int __VERIFIER_nondet_int(void);

int use(char *p) { return p == 0; }

int main() {
  char buf[4] = {0};
  int k = __VERIFIER_nondet_int();
  return use(buf + (k + 1));
}
