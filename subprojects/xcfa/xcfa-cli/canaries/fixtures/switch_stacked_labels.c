// `case 1: case 2:` is one statement with two labels: both select it, neither is the default.
extern int __VERIFIER_nondet_int(void);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "switch_stacked_labels.c", 3, "reach_error"); }

int main(void) {
  int r = __VERIFIER_nondet_int();
  int h = 0;
  switch (r) {
  case 1:
  case 2:
    h = 12;
    break;
  default:
  case 3:
    h = 99;
  }
  if (r == 1 && h != 12)
    reach_error();
  if (r == 2 && h != 12)
    reach_error();
  if (r == 3 && h != 99)
    reach_error();
  if (r == 4 && h != 99)
    reach_error();
  return 0;
}
