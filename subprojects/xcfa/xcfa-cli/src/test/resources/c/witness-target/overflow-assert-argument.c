extern void abort(void);
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!cond) {
    abort();
  }
}
int main(void) {
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  // an argument is not a full expression, the call statement is
  __VERIFIER_assert(x + y != 7); // target: __VERIFIER_assert(x + y != 7)
  return 0;
}
