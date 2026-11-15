// As 44forward_known_branch_unsafe.c, but the known condition excludes the error.
extern int __VERIFIER_nondet_int(void);
extern void reach_error(void);

int main(void) {
  int x = 3;
  int *p = &x;
  if (*p == 4) {
    if (__VERIFIER_nondet_int()) reach_error();
  }
  return 0;
}
