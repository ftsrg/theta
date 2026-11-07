// Three iterations of loop_safe.c without the loop.
extern int __VERIFIER_nondet_int(void);
extern void abort(void);
void reach_error() { abort(); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); } }
void assume_abort_if_not(int cond) { if (!cond) { abort(); } }
int a, b, c, last;

int main() {
  last = a;
  b = __VERIFIER_nondet_int();
  assume_abort_if_not(b > -1000 && b < 1000);
  if (b > 10) { if (last > 0) a = b + 1; else a = b - 1; } else { a = last; }
  if (a > 100) c = 1; else c = 0;
  if (b < 0) { if (c) a = a + 1; }
  last = a;
  b = __VERIFIER_nondet_int();
  assume_abort_if_not(b > -1000 && b < 1000);
  if (b > 10) { if (last > 0) a = b + 1; else a = b - 1; } else { a = last; }
  if (a > 100) c = 1; else c = 0;
  if (b < 0) { if (c) a = a + 1; }
  last = a;
  b = __VERIFIER_nondet_int();
  assume_abort_if_not(b > -1000 && b < 1000);
  if (b > 10) { if (last > 0) a = b + 1; else a = b - 1; } else { a = last; }
  if (a > 100) c = 1; else c = 0;
  if (b < 0) { if (c) a = a + 1; }
  __VERIFIER_assert(
      (b < 0 && c) || ((b > 10 ? (last > 0 ? a == b + 1 : a == b - 1) : a == last) && c == (a > 100)));
}
