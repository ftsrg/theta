// `__builtin_nanf` and the NaN-safe comparison builtins have no declaration to resolve, so a
// file using one died in the frontend. The comparisons already had exact models under their
// plain names (FpFunctionsToExprsPass), so only the `__builtin_` spelling needed aliasing.
//
// The checks pin NaN semantics rather than mere parsing: `n == n` being *false* is true of NaN
// and of no other value, and the ordered comparisons must all be false against a NaN while
// still behaving normally on ordinary operands -- which is the whole point of these builtins.
// The NaN payload string is ignored by design; nothing here can observe it.
extern void abort(void);
void reach_error(){ abort(); }

int main() {
  float n = __builtin_nanf("");
  double dn = __builtin_nan("");

  /* NaN is the only value not equal to itself */
  if (n == n) reach_error();
  if (dn == dn) reach_error();
  if (!__builtin_isnan(n)) reach_error();

  /* every ordered comparison against a NaN is false */
  if (__builtin_isgreater(n, 1.0f)) reach_error();
  if (__builtin_isgreaterequal(n, 1.0f)) reach_error();
  if (__builtin_isless(n, 1.0f)) reach_error();
  if (__builtin_islessequal(n, 1.0f)) reach_error();
  if (__builtin_islessgreater(n, 1.0f)) reach_error();

  /*... and unordered is true for exactly that case */
  if (!__builtin_isunordered(n, 1.0f)) reach_error();
  if (__builtin_isunordered(1.0f, 2.0f)) reach_error();

  /* ordinary operands still compare normally */
  if (!__builtin_isless(1.0f, 2.0f)) reach_error();
  if (!__builtin_islessequal(2.0f, 2.0f)) reach_error();
  if (!__builtin_isgreater(3.0f, 2.0f)) reach_error();

  /* a NaN is not infinite, and an infinity is not a NaN */
  if (__builtin_isnan(__builtin_inff())) reach_error();

  return 0;
}
