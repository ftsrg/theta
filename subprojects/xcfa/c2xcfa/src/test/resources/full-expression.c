extern int __VERIFIER_nondet_int(void);
int main() {
  int x = __VERIFIER_nondet_int();
  while (x > 0 && x < 10) { // full expression: x > 0 && x < 10
    x--; // statement: x--
  }
  x = x * 2; // statement: x = x * 2
  if (x + 1 > 3) { // full expression: x + 1 > 3
    return 1;
  }
  int y = x * 3; // full expression: x * 3
  return y + 2; // full expression: y + 2
}
