// An unparenthesized `?:` as an array index selects by its guard: `a[c ? 1 : 0]` used to read
// `a[0]` whatever `c` was, so this unsafe program was reported safe.
extern int __VERIFIER_nondet_int(void);
extern void abort(void);
void reach_error() { abort(); }

int main() {
  int n = __VERIFIER_nondet_int();
  int a[2] = {0, 1};
  if (a[(n > 7) ? 1 : 0] == 1) reach_error();
  return 0;
}
