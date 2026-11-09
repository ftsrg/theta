extern int __VERIFIER_nondet_int(void);
void reach_error() {}

int main() {
  int x = __VERIFIER_nondet_int();
  int y;
  if (x > 10) {
    y = 1;
  } else {
    y = 2;
  }
  if (x > 20) {
    y = y + 2;
  }
  if (y == 0) {
    reach_error();
  }
  return 0;
}
