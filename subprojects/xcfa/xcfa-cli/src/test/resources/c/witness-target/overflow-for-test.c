extern int __VERIFIER_nondet_int(void);
int main(void) {
  int y = __VERIFIER_nondet_int();
  int i;
  if (y < 0) return 0;
  for (i = 1; i + y < 10; i++) { // target: i + y < 10
  }
  return 0;
}
