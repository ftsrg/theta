// The false branch of `?:` is a conditional-expression, not an expression (C11 6.5.15), so it must
// not absorb the arguments after it: `f(c ? a : b, x, y)` used to parse as a one-argument call, and
// inlining `f` then refused the arity mismatch (ldv `dma_alloc_attrs(p ? &p->dev : 0, ...)`).
extern void abort(void);
void reach_error() { abort(); }

static int f(int a, int b, int c) { return a * 100 + b * 10 + c; }

int main() {
  int c = 1;
  if (f(c ? 1 : 2, 3, 4) != 134) reach_error();
  if (f(5, c ? 6 : 7, 8) != 568) reach_error();
  if (f(!c ? 1 : !c ? 2 : 3, 0, 9) != 309) reach_error();
  return 0;
}
