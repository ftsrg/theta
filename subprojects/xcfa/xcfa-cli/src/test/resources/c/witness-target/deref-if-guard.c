extern int __VERIFIER_nondet_int(void);
int main(void) {
  int a[2] = {0, 0};
  int i = __VERIFIER_nondet_int();
  if (i < 0 || i > 5) {
    return 0;
  }
  if (a[i] == 1) { // target: a[i] == 1
    return 1;
  }
  return 0;
}
