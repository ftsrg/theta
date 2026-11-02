extern int __VERIFIER_nondet_int(void);
int main(void) {
  int y = 1;
  while (1) {
    y = y + 2 * __VERIFIER_nondet_int(); // target: y = y + 2 * __VERIFIER_nondet_int()
    if (y == 0) {
      return 0;
    }
  }
}
