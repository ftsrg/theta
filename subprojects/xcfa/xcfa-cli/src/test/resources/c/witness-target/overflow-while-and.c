extern int __VERIFIER_nondet_int(void);
int main(void) {
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  while (x > 0 && x + y > 0) { // target: x > 0 && x + y > 0
    x--;
  }
  return 0;
}
