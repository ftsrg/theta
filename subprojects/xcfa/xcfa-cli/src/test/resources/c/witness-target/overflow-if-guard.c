extern int __VERIFIER_nondet_int(void);
int main(void) {
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  if (x + y <= 0) { // target: x + y <= 0
    return 1;
  }
  return 0;
}
