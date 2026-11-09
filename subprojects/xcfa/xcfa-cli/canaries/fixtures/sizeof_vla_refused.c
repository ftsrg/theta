// The size of a VLA is not modelled: sizeof has to refuse it rather than report a wrong constant.
extern int __VERIFIER_nondet_int(void);

int main() {
  int n = __VERIFIER_nondet_int();
  if (n < 1 || n > 5) return 0;
  int a[n];
  return sizeof(a) == 0;
}
