// The `+` is evaluated only when the guard rules out the overflow.
extern int __VERIFIER_nondet_int(void);

int main() {
  int x = __VERIFIER_nondet_int();
  int r = (x < 2147483647) ? x + 1 : 0;
  return r;
}
