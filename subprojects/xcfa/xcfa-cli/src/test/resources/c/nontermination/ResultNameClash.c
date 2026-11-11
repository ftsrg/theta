extern int __VERIFIER_nondet_int(void);

int step(int input) {
  if (input == 1) {
    return 2;
  }
  return 1;
}

int main() {
  int expected = 1;
  while (1) {
    int input = __VERIFIER_nondet_int();
    if (input != expected) {
      return 0;
    }
    expected = step(input);
  }
}
