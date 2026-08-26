// `a - b` where b is INT_MIN. The true result is in range, so this program has no overflow --
// but under `--arithmetic bitvector` it was reported as one.
//
// A bitvector operation has already wrapped, so overflow is detected by redoing it one bit wider
// and checking the two agree. C spells `a - b` as an n-ary `(+ a (- b))`, so the subtrahend reaches
// the check as a negation, and it was widened as `SExt(bvneg b)` -- negating at the NARROW width,
// where it wraps: `bvneg INT_MIN == INT_MIN`. For b == INT_MIN the "exact" reference value became
// `a - 2^31` instead of `a + 2^31`, the two sides disagreed, and a spurious overflow fired. The
// widening now happens before the negation, where nothing wraps.
//
// This is what made the whole `c/weaver/chl-*.wvr` family answer `false(no-overflow)` on safe
// programs under bitvector (14 wrong runs in the batch-89 `pred_bvms` run): their `minus()` helper
// guards `a - b` and is called with unconstrained ints, so b == INT_MIN is reachable.
//
// The guarded form below is the actual `minus()` shape and is the one that regressed; the bare form
// above it is the minimal witness. Both must be SAFE.
extern void abort(void);
void reach_error() { abort(); }
extern int __VERIFIER_nondet_int(void);

int main() {
  /* minimal witness: -1 - INT_MIN == 2147483647, in range */
  int a = __VERIFIER_nondet_int();
  int b = __VERIFIER_nondet_int();
  if (a != -1) return 0;
  if (b != -2147483647 - 1) return 0;
  int d = a - b;
  if (d != 2147483647) reach_error();

  /* the `minus()` shape: guards make the subtraction provably in range for every a, b */
  int p = __VERIFIER_nondet_int();
  int q = __VERIFIER_nondet_int();
  if (!(q <= 0 || p >= q - 2147483648)) return 0;
  if (!(q >= 0 || p <= q + 2147483647)) return 0;
  return p - q;
}
