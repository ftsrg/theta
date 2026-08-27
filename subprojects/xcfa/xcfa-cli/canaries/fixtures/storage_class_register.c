// `register` and `auto` were refused outright, which kills the whole frontend on any file
// that merely uses the keyword. Neither carries
// semantics this model represents: `auto` is the default storage class for a block-scope
// object, and `register` is a placement hint whose only observable effect is that `&x` is
// ill-formed. Ignoring that is the safe direction -- it lets more programs through rather
// than changing the meaning of any that compile. `_Thread_local` stays refused: per-thread
// copies are a real semantic difference.
extern void abort(void);
void reach_error(){ abort(); }
extern int __VERIFIER_nondet_int(void);
static int helper(register int a, register int b) { return a + b; }
int main() {
  register int i;
  auto int j = 3;
  register int sum = 0;
  for (i = 0; i < 4; i++) { register int t = i * 2; sum += t; }
  if (sum != 12) reach_error();
  if (j != 3) reach_error();
  if (helper(2, 5) != 7) reach_error();
  return 0;
}
