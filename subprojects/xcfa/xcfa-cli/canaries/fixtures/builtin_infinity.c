// The GCC infinity builtins have no declaration to resolve, so a file using one died as
// "No such variable or macro: __builtin_inff" before anything else could run -- and they are
// ordinary in float benchmarks (`isgreater(__builtin_inff(), 1.0)` is the sort of thing being
// tested there).
//
// The checks below pin the *value*, not just that it parses. Each identity holds for a true
// infinity and for nothing else: a finite stand-in (however large) fails `x * 2 == x`, and a
// zero or garbage value fails `1 / x == 0`. `__builtin_inf` is deliberately included next to
// `__builtin_inff` because its name ends in `f` while it is the *double* one -- sniffing the
// suffix instead of spelling the names out would hand back a float infinity for it.
extern void abort(void);
void reach_error(){ abort(); }

int main() {
  float finf = __builtin_inff();
  double dinf = __builtin_inf();
  float fhuge = __builtin_huge_valf();
  double dhuge = __builtin_huge_val();

  /* larger than any finite value of the type */
  if (!(finf > 3.4e38f)) reach_error();
  if (!(dinf > 1.7e308)) reach_error();

  /* absorbing under multiplication -- only infinity does this */
  if (!(finf * 2.0f == finf)) reach_error();
  if (!(dinf * 2.0 == dinf)) reach_error();

  /* a finite value over infinity underflows to zero */
  if (!(1.0f / finf == 0.0f)) reach_error();
  if (!(1.0 / dinf == 0.0)) reach_error();

  /* huge_val is the same value, spelled differently */
  if (!(fhuge == finf)) reach_error();
  if (!(dhuge == dinf)) reach_error();

  /* the double one really is double-width: it exceeds every finite float */
  if (!(dinf > 3.4e38)) reach_error();

  return 0;
}
