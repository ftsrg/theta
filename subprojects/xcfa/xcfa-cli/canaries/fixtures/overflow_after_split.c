// `ReferenceElimination` rebuilds every expression in a procedure once that procedure has
// any base/offset-split variable, and `FrontendMetadata` is keyed by object identity -- so
// every arithmetic node came out with no `cType`. `OverflowDetectionPass` only instruments
// nodes whose `cType` is a signed integer, so it silently emitted *no checks at all* and
// no-overflow became vacuously true for the whole procedure. One `&p->a` was enough
// (ldv-regression/test22-2, array-memsafety/add_last-alloca-1, the stroeder pair).
extern int __VERIFIER_nondet_int(void);
extern _Bool __VERIFIER_nondet_bool(void);

struct S {
  int a, b;
};
struct S s1, s2;

struct S *pick() { return __VERIFIER_nondet_bool() ? &s1 : &s2; }

int main() {
  int k = __VERIFIER_nondet_int();
  struct S *p = pick();
  int *pa = &p->a; // forces the base/offset split
  int m = k - 10;  // k is any int, so this really can overflow
  return m + *pa;
}
