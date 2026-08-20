// NOT REGISTERED in fixtures.tsv: theta gets this WRONG today, so it may not be a fixture.
// It is the known cost of the fp<->bits round trip (commit f470a74ddf), kept as the repro.
//
//   ./theta-start.sh union_nan_payload_bytes_KNOWN_WRONG.c --svcomp --portfolio COMPLEX27 \
//     --loglevel RESULT --property .../unreach-call.prp --architecture ILP32 \
//     --memory-model bytes --arithmetic bitvector
//
// gcc: SAFE (a plain load/store of a double preserves the NaN payload on x86).
// theta: `SafetyResult Unsafe` -- a spurious counterexample.
//
// Why: `fpToIEEEBV` is unspecified for NaN, so ByteMemoryPass pins a NaN to the canonical quiet
// encoding on the way into the bytes. That makes the conversion a function, which is what stops a
// NaN from silently becoming a normal number -- but it also DESTROYS the payload, so the 0x2A
// below is gone after the value makes a round trip through the float view.
//
// ⚠️ This is a REGRESSION introduced by that commit, and measured as such: before it, a float write
// did not touch the byte cells at all, so the payload written through the integer view simply
// survived and this program verified Safe -- by accident, not by soundness (the same non-aliasing
// made `u.value = 1.0; u.parts.msw` come back unconstrained and answer Unsafe). The fix trades a
// broad wrong-answer class for this narrow one; it is net positive, not strictly better.
//
// No cheap fix exists: getting the payload right needs an exact to-bits direction, and SMT-LIB does
// not specify one. Peeling `ToIeeeBv(FromIeeeBv(b))` would only catch the case where the write's
// right-hand side is syntactically the read, which it is not here -- the value goes through a
// local variable first.
//
// Not reachable in any shipped configuration: `bytes` requires an explicit --memory-model, and the
// automatic fallback to it is deliberately unshipped.
extern void abort(void);
void reach_error() { abort(); }
typedef union { double value; unsigned int words[2]; } d_t;
int main() {
  d_t u;
  /* a NaN with a specific payload, built through the integer view */
  u.words[1] = 0x7FF80000u;   /* quiet NaN, exponent all ones */
  u.words[0] = 0x2Au;         /* payload 42 */
  double d = u.value;         /* read it out as a double ... */
  u.value = d;                /* ... and write it straight back */
  if (u.words[0] != 0x2Au) reach_error();   /* payload preserved? */
  return 0;
}
