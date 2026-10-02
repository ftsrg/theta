// As 14sequential_loops_unsafe.c, but the error needs a 4th iteration of the second loop, which
// no unrolling reaches: safe once neither unroll exit is reachable.
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
  if (cnt >= 4) reach_error();
  return 0;
}
