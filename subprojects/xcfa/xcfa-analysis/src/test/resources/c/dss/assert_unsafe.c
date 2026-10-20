extern int __VERIFIER_nondet_int(void);
void assert(int cond);

int main() {
  int x = __VERIFIER_nondet_int();
  if (x > 5) {
    assert(x < 10);
  }
  return 0;
}
