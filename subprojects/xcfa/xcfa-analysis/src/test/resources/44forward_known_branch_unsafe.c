// The condition read through the pointer is known: only the branch it selects is followed.
extern int __VERIFIER_nondet_int(void);
extern void reach_error(void);

int main(void) {
  int x = 3;
  int *p = &x;
  if (*p == 3) {
    if (__VERIFIER_nondet_int()) reach_error();
  }
  return 0;
}
