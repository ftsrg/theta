// C evaluates `x + a - b - 1` left to right as `((x + a) - b) - 1`, but it reaches
// OverflowDetectionPass as ONE flattened n-ary node, `(+ x a (- b) (- 1))`. Only the final value
// was range-checked, so an overflow in an intermediate was invisible.
//
// Here `a == b` makes the whole chain worth `x - 1`, which with `x >= 0` never overflows -- while
// the intermediate `x + a` overflows at `x = a = INT_MAX`. theta answered `true` (safe) on a task
// whose expected verdict is `false`: termination-crafted/Stockholm-2 and
// termination-nla/dijkstra6-both-nt, the -32 class.
//
// The guard and the full chain are both needed to expose it: without `a == b` the final sum itself
// can overflow and was already caught, and a two-operand `x + a` has no intermediate to lose.
extern int __VERIFIER_nondet_int(void);

int main() {
  int x = __VERIFIER_nondet_int();
  int a = __VERIFIER_nondet_int();
  int b = __VERIFIER_nondet_int();
  if (a == b) {
    while (x >= 0) {
      x = x + a - b - 1;   /* the intermediate x + a overflows */
    }
  }
  return 0;
}
