// The selected branch of `?:` overflows for large `x`.
extern int __VERIFIER_nondet_int(void);

int main() {
  int x = __VERIFIER_nondet_int();
  int r = (x > 0) ? x + 2147483647 : 0;
  return r;
}
