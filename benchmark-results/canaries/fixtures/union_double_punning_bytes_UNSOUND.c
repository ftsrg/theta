// NOT REGISTERED in fixtures.tsv, deliberately: theta gets this WRONG today, and a fixture may
// only encode behaviour we want. This file is the repro for that bug, kept next to the fixtures so
// whoever fixes the byte-addressed memory model has the case to hand.
//
// Run it with:
//   ./theta-start.sh union_double_punning_bytes_UNSOUND.c --svcomp --portfolio COMPLEX27 \
//     --loglevel RESULT --property .../unreach-call.prp --architecture ILP32 \
//     --memory-model bytes --arithmetic bitvector
//
// Expected SAFE. theta answers `SafetyResult Unsafe` -- a spurious counterexample. gcc is the
// oracle and agrees with the assertion below:
//   1.0 -> msw=0x3FF00000 lsw=0x00000000
// Reading the bytes of a double that was written AS a double comes back unconstrained, so any
// program that checks those bits gets a false alarm. The union is internally consistent
// (`u.words[1] == u.parts.msw` verifies Safe), so it is specifically the double->bytes encoding
// that is missing, not the union layout.
//
// Why this matters beyond the bytes model: the cell-per-value models REFUSE this program
// ("Accessing member [...] of a byte-addressed union is not supported: a floating-point member is
// not supported"), and that refusal exists precisely because the fp<->bits round trip is unsound
// (the batch-59 NaN gate on fpToIEEEBV). The byte-addressed model does not fix the round trip --
// it just does not check. So an automatic fallback to `--memory-model bytes` on that refusal, which
// is what batch-92 item 10 set out to build, would convert ~554 loud ERRORs (score 0, the
// float-newlib and float-benchs families) into confident WRONG `false` verdicts at -16 apiece.
// The fallback was implemented, measured against this file, and dropped for that reason.
//
// Fix the fp<->bytes encoding first; then the fallback becomes worth building.
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
