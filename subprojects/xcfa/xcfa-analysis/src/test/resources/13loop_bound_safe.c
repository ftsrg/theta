// The loop runs at most 5 times, but its trip count is not known statically: it is force unrolled,
// and the safe verdict only holds once the unroll exit (a 6th iteration) is shown unreachable.
extern int __VERIFIER_nondet_int(void);
extern void reach_error(void);

int main(void) {
  int n = __VERIFIER_nondet_int();
  if (n > 5 || n < 0) return 0;
  int i = 0;
  while (i < n) i++;
  if (i > 5) reach_error();
  return 0;
}
