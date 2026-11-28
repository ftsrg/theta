extern int __VERIFIER_nondet_int(void);
void reach_error() {}

void check(int c) {
  int d = c;
  if (!d) {
    reach_error();
  }
}

int main() {
  int n = __VERIFIER_nondet_int();
  int x = 0;
  while (x < n) {
    x++;
  }
  check(n < 0 || x == n);
  return 0;
}
