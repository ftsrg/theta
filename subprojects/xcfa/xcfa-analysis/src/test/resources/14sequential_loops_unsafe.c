// The second loop can only iterate 3 times once the first one has iterated 5 times. Its unroll exit
// is unreachable until the first loop is unrolled deep enough, so it must not be cut for good.
extern int __VERIFIER_nondet_int(void);
extern void reach_error(void);

int main(void) {
  int c = 0;
  while (__VERIFIER_nondet_int() && c < 5) c++;
  int cnt = 0;
  while (c >= 3) {
    c--;
    cnt++;
  }
  if (cnt >= 3) reach_error();
  return 0;
}
