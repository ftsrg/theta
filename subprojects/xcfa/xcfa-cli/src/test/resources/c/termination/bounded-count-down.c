extern int __VERIFIER_nondet_int(void);

int main() {
  int i = __VERIFIER_nondet_int();
  if (i < 0 || i > 3) return 0;
  while (i > 0) {
    i = i - 1;
  }
  return 0;
}
