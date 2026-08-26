// A program whose ONLY bit manipulation is compound (`|=`, `&=`, `^=`, `<<=`, `>>=`) and never
// binary (`|`, `&`, `^`, `<<`, `>>`, `~`). That distinction was the whole bug.
//
// Under `--arithmetic efficient` the frontend picks the encoding up front: BitwiseChecker gathers
// the arithmetic traits and FunctionVisitor resolves `efficient` to bitvector if any bit
// manipulation was seen, integer otherwise. But the checker only ever visited the *binary*
// expression rules -- the grammar routes a compound assignment through `assignmentOperator`
// instead, so a program like this one looked purely arithmetic. Integer arithmetic was chosen, and
// then CAssignment refused the very first `|=`: "only modelled over bitvectors" -- rejecting the
// program for an encoding this code had itself selected.
//
// The fallback in XcfaParser that exists to retry with bitvectors could not save it either: it
// required the arithmetic to still read `efficient`, which it never does by the time a parse fails.
// So the retry was dead for exactly the programs it was written for.
//
// This is `|=` in the coreutils-v9.5-units `relpath_*` family (20 runs in the batch-94 parse run),
// where every one of them accumulates an error flag as `buf_err |= f(...)`.
extern void abort(void);
void reach_error() { abort(); }
extern unsigned int __VERIFIER_nondet_uint(void);

int main() {
  unsigned int x = __VERIFIER_nondet_uint();

  /* the error-flag accumulation shape that motivated this */
  int err = 0;
  err |= (x > 100);
  err |= (x < 10);
  if (x >= 10 && x <= 100 && err) reach_error();

  /* each compound operator, against a known value */
  unsigned int v = 0xF0F0F0F0u;
  v &= 0xFF00FF00u;                      /* 0xF000F000 */
  if (v != 0xF000F000u) reach_error();
  v |= 0x000F000Fu;                      /* 0xF00FF00F */
  if (v != 0xF00FF00Fu) reach_error();
  v ^= 0xFFFFFFFFu;                      /* 0x0FF00FF0 */
  if (v != 0x0FF00FF0u) reach_error();
  v >>= 4;                               /* 0x00FF00FF */
  if (v != 0x00FF00FFu) reach_error();
  v <<= 8;                               /* 0xFF00FF00 */
  if (v != 0xFF00FF00u) reach_error();

  /* and on a symbolic value: masking the low nibble off, then setting bit 0, leaves it odd.
     Written with compound operators only -- a single binary `>>` anywhere in this file would
     make the old checker see the program as bitwise and the fixture would stop discriminating. */
  unsigned int m = x;
  m &= 0xFFFFFFF0u;
  m |= 1u;
  unsigned int lo = m;
  lo &= 0xFu;
  if (lo != 1u) reach_error();

  return 0;
}
