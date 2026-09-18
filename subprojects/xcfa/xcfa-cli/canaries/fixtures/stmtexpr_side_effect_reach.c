// A GNU statement expression that yields no value still runs its statements for their side effects.
// The frontend used to queue them only on the value-producing path, so a reach_error() inside such a
// block was dropped and the error location became unreachable. x may be non-zero, so the call is
// reachable and the expected verdict is UNSAFE.
extern void abort(void);
extern int __VERIFIER_nondet_int(void);
void reach_error(void) { abort(); }
int main(void) {
  int x = __VERIFIER_nondet_int();
  ({
    if (x) {
      reach_error();
    }
  });
  return 0;
}
