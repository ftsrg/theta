extern int __VERIFIER_nondet_int(void);

int main() {
  int a[1];
  a[0] = __VERIFIER_nondet_int();
  while (a[0] > 0) {
    a[0] = a[0] - 1;
  }
  return 0;
}
