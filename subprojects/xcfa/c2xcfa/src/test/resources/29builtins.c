// Pure-passthrough GCC builtins have no declaration to resolve and used to fail
// with "No such variable or macro: __builtin_expect". They have exact semantics:
// __builtin_expect(exp, c) == exp; __builtin_constant_p(runtime value) == 0.
extern void abort(void);
extern void reach_error(void);

int main() {
  int y = 7;
  if (!__builtin_expect(y == 7, 1)) {
    reach_error();
    abort();
  }
  if (__builtin_constant_p(y) != 0) {
    reach_error();
    abort();
  }
  double d = 1.0;
  if (__builtin_isnan(d) || !__builtin_isfinite(d)) {
    reach_error();
    abort();
  }
  return 0;
}
