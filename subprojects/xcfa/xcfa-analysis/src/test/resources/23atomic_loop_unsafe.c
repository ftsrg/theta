// The loop inside the atomic block is force unrolled: its unroll exit must survive the removal of
// atomic abort branches, or the safe verdict of the initial bound would count as final.
extern int __VERIFIER_nondet_int(void);
extern void reach_error(void);

int x = 0;

void __VERIFIER_atomic_count(void) {
  while (__VERIFIER_nondet_int()) x++;
}

int main(void) {
  __VERIFIER_atomic_count();
  if (x == 5) reach_error();
  return 0;
}
