// `memset` with a byte count that is not known at build time. MemoryFunctionsPass has implemented
// memset for a long while, but only by spelling out one assignment per element -- which needs the
// count. A symbolic one was declined, and a declined call is left in place as an InvokeLabel to a
// procedure that does not exist, so it surfaced as "No such method memset" even though the pass had seen the call and chosen not to model it.
//
// It is now lowered to a real loop over the elements the count covers,
// `for (i = 0; i < n / sizeof *dst; i++) dst[i] = c`. Translating the byte count into an element
// count is an ordinary division; it needs nothing known at build time and no byte-granular memory.
//
// The straddled tail element -- when n is not a whole number of elements -- is havoc'd rather than
// skipped: leaving it holding its old value would be a specific WRONG value, able to hide a bug as
// easily as invent one. That havoc is guarded on `count * w == n`, so the exact case (which is what
// `memset(p, 0, n * sizeof *p)` is) keeps full precision.
//
// ⚠️ This runs after LoopUnrollPass, so the loop is never unrolled: CEGAR must find an invariant for
// it and currently times out, while KIND/BMC/IMC answer it. The fixture is therefore SAFE-expected
// via the portfolio, which reaches a loop-capable configuration.
extern void abort(void);
void reach_error() { abort(); }
extern void *malloc(unsigned long);
extern void *memset(void *, int, unsigned long);
extern int __VERIFIER_nondet_int(void);

int main() {
  int n = __VERIFIER_nondet_int();
  if (n < 1 || n > 8) return 0;
  int *p = (int *)malloc(n * sizeof(int));
  if (!p) return 0;
  memset(p, 0, n * sizeof(int)); /* symbolic byte count */
  if (p[0] != 0) reach_error();
  return 0;
}
