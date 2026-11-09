// A call through a function-pointer table indexed by `?:` dispatches to the selected element:
// `tbl[c ? 1 : 0](x)` used to call `tbl[0]` only.
extern int __VERIFIER_nondet_int(void);
extern void abort(void);
void reach_error() { abort(); }

static void bad(unsigned int t) { reach_error(); }
static void nop(unsigned int t) { (void)t; }

int main() {
  int n = __VERIFIER_nondet_int();
  void (*tbl[2])(unsigned int) = {nop, bad};
  tbl[(n > 7) ? 1 : 0]((unsigned int)n);
  return 0;
}
