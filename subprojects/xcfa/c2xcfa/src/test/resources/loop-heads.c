extern int __VERIFIER_nondet_int(void);
int g;
int main() {
  int n = __VERIFIER_nondet_int();
  int x = 0;
  while (x < n) { // loop g n x
    int inner = x;
    x = inner + 1;
  }
  for (int i = 0; i < n; i++) { // loop g n x i
    g++;
  }
  do { // loop g n x
    x--;
  } while (x > 0);
  for (;;) { // loop g n x
    if (__VERIFIER_nondet_int()) break;
  }
  return 0;
}
