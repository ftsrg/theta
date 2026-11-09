extern int __VERIFIER_nondet_int(void);

int main() {
  int a[2];
  a[1] = __VERIFIER_nondet_int();
  while (a[1] >= 0) {
    a[1] = a[1] - 1;
    a[1] = __VERIFIER_nondet_int();
  }
  return 0;
}
