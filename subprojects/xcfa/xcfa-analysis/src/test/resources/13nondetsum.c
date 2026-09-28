extern void reach_error();
extern int __VERIFIER_nondet_int();
int main() {
  int i = 0, s = 0;
  int n = __VERIFIER_nondet_int();
  if (n < 0 || n > 10) return 0;
  while (i < n) { if (__VERIFIER_nondet_int()) s += 2; else s += 1; i++; }
  if (s == 7 && n == 4) reach_error();
  return 0;
}
