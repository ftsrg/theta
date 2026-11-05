// An address-taken local dies when its function returns, also on an early `return` that skips
// the end of its block.
extern void abort(void);
extern int __VERIFIER_nondet_int(void);

int *f(int c) {
  int a = 1;
  int *p = &a;
  if (c) return p;
  return 0;
}

int main() {
  int *r = f(__VERIFIER_nondet_int());
  if (r != 0 && *r != 1) abort();
  return 0;
}
