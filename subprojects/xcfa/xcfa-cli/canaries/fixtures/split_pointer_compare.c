// `&a[i]` is split into base and offset; `a + i` must compare equal to it, not to base `a + i`.
extern void abort(void);
void reach_error() { abort(); }
extern int __VERIFIER_nondet_int(void);

int a[4];

int main() {
  int i = __VERIFIER_nondet_int();
  if (i < 0 || i > 3) return 0;
  if (&a[2] != a + 2) reach_error();
  if (&a[i] != a + i) reach_error();
  int *p = &a[1];
  if (p + 1 != &a[2]) reach_error();
  if (&a[2] == a + 3) reach_error();
  return 0;
}
