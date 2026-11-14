// The read's index has two values after the merge: both cells stay candidates.
extern int __VERIFIER_nondet_int(void);
extern void reach_error(void);

int a[3];

int main(void) {
  int i = __VERIFIER_nondet_int() ? 0 : 2;
  a[0] = 1;
  a[2] = 5;
  if (a[i] == 5) reach_error();
  return 0;
}
