extern int __VERIFIER_nondet_int(void);
void reach_error() {}

int main() {
  int n = __VERIFIER_nondet_int();
  int x = 0;
  while (x < n) {
    x++;
  }
  if (n >= 0 && x != n) {
    reach_error();
  }
  return 0;
}
