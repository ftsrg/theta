// NOT REGISTERED in fixtures.tsv: the harness has no --memory-model column, so this cannot be run
// as a fixture. Kept as the standing evidence for why the byte-addressed model REFUSES floats.
//
//   ./theta-start.sh union_double_punning_bytes_REFUSED.c --svcomp --backend NONE --loglevel RESULT \
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

typedef union {
  double value;
  struct {
    unsigned int lsw;
    unsigned int msw;
  } parts;
  unsigned int words[2];
} ieee_double;

int main() {
  ieee_double u;

  u.value = 1.0; /* 0x3FF0000000000000 */
  if (u.parts.msw != 0x3FF00000u) reach_error(); /* theta reports this reachable; gcc does not */
  if (u.parts.lsw != 0u) reach_error();

  /* this half DOES verify Safe -- the union's own layout is consistent */
  if (u.words[1] != u.parts.msw) reach_error();

  return 0;
}
