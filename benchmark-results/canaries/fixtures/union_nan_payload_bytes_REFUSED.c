// NOT REGISTERED in fixtures.tsv: the harness has no --memory-model column, so this cannot be run
// as a fixture. Kept as the standing evidence for why the byte-addressed model REFUSES floats.
//
//   ./theta-start.sh union_nan_payload_bytes_REFUSED.c --svcomp --backend NONE --loglevel RESULT \
//     --property .../unreach-call.prp --architecture ILP32 \
//     --memory-model bytes --arithmetic bitvector
//
// Expected today: exit 210, "A floating-point object ((Fp 11 53)) in byte-addressed memory is not
// supported". A refusal, deliberately -- NOT a verdict.
//
// Why floats are refused there: splitting one into byte cells routes it through the IEEE bit
// reinterpretation, and SMT-LIB leaves that underspecified for NaN. Measured against z3 4.12.6:
//   * a NaN's bits may differ from the canonical quiet pattern            -> sat
//   * two distinct NaNs must share their bits (so payloads collapse)      -> unsat
//   * a payload round trip may lose the payload ... or keep it            -> sat / sat
// The last pair is the problem: the choice is the solver's, and in a verification query it takes
// whichever falsifies the property. A program inspecting those bits would get a spurious
// counterexample -- a wrong `false` (-16) where a refusal scores 0.
//
// History worth keeping: this pass once left floats in an array of their own, which is the same
// limitation held SILENTLY -- a double and the bytes overlapping it were unrelated storage, so
// `u.value = 1.0; u.parts.msw` read cells nothing had written. Then it did the round trip, which
// fixed ordinary values but made NaN payloads wrong. Refusing says the true thing out loud.
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
