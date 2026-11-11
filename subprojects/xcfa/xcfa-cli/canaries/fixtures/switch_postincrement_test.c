// The labels of `switch (i++)` compare the value before the increment, on every path.
extern int __VERIFIER_nondet_int(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "switch_postincrement_test.c", 3, "reach_error"); }

int main(void) {
  int i = 1;
  int h = 0;
  switch (i++) {
  case 1:
    h = 1;
    break;
  case 2:
    h = 2;
  }
  if (h != 1 || i != 2)
    reach_error();
  switch (i++) {
  case 1:
    h = 3;
  }
  if (h != 1 || i != 3)
    reach_error();
  return 0;
}
