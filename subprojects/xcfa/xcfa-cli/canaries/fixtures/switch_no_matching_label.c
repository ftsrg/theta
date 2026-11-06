// A switch without a default skips its body when no label matches: that path has to exist.
extern int __VERIFIER_nondet_int(void);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "switch_no_matching_label.c", 3, "reach_error"); }

int main(void) {
  int r = __VERIFIER_nondet_int();
  int h = 0;
  switch (r) {
  case 1:
    h = 1;
    break;
  case 2:
    h = 2;
  }
  if (r == 7 && h == 0)
    reach_error();
  return 0;
}
