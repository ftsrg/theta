// `?:` as a __builtin_expect argument or a case label selects by its guard; both used to take
// the false branch.
extern int __VERIFIER_nondet_int(void);
extern void abort(void);
void reach_error() { abort(); }

int main() {
  int n = __VERIFIER_nondet_int();
  if (n != 9) return 0;
  if (!__builtin_expect(n > 7 ? 1 : 0, 0)) reach_error();
  switch (n) {
  case (1 ? 9 : 8):
    break;
  default:
    reach_error();
  }
  return 0;
}
