// The second write executes only on one branch, so it does not hide the first from the read.
extern int __VERIFIER_nondet_int(void);
extern void reach_error(void);

int a[4];

int main(void) {
  int *p = &a[1];
  *p = 1;
  if (__VERIFIER_nondet_int()) *p = 2;
  if (a[1] == 1) reach_error();
  return 0;
}
