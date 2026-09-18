// Z3 emits `(_ bit2bool k) x` when it reasons about individual bits of a bitvector: the term is
// true exactly when bit k of x is set. theta's Z3 back-transformation had no entry for it, so it
// fell through to toFuncLitExpr, which needs a model, and threw
// `NullPointerException: Unsupported function 'bit2bool'` when there was none.
//
// It was the largest single failure of the bitvector encoding, across many unrelated families --
// and easy to dismiss as task-specific when it first shows up on one program.
//
// This fixture forces bit-level reasoning on a program small enough to actually finish, so the
// handler has to round-trip to a verdict rather than merely not crash. Companion checks that were
// run by hand cover the other direction (an UNSAFE case where bit 3 set is reachable, and
// `y = x | 1` never equalling an even constant), so an inverted comparison cannot pass all three.
extern void abort(void); void reach_error(){ abort(); }
extern unsigned int __VERIFIER_nondet_uint(void);
int main(){ unsigned int x = __VERIFIER_nondet_uint();
  if ((x & 1u) == 1u) { if ((x & 1u) == 0u) reach_error(); }
  return 0; }
