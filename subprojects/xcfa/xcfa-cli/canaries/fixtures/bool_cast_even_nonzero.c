// Conversion to _Bool is a comparison against zero (C11 6.3.1.2), not truncation to bit 0. The
// bitvector CastVisitor used to emit Extract(x,0,1), so every even non-zero value became false and
// assume_abort_if_not on an even value killed the path, hiding a reachable error.
// The bitwise ops force the bitvector arm; x is even and >= 2, so the assumption always holds.
extern void abort(void);
extern unsigned int __VERIFIER_nondet_uint(void);
void reach_error(void) { abort(); }
void __VERIFIER_assert(_Bool cond) {
  if (!cond) {
    reach_error();
  }
}
void assume_abort_if_not(_Bool cond) {
  if (!cond) {
    abort();
  }
}
int main(void) {
  unsigned int x = (__VERIFIER_nondet_uint() | 2u) & ~1u;
  assume_abort_if_not(x);
  __VERIFIER_assert(0);
  return 0;
}
