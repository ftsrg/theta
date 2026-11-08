// Pointers are compared and selected as full-width addresses: `b` and `b + 3` lie on either side
// of 2^31, where an int view of them changes sign.
extern void abort(void);
void reach_error() { abort(); }
extern int __VERIFIER_nondet_int(void);

int main() {
  int n = __VERIFIER_nondet_int();
  if (n < 1) n = 1;
  char *a = (char *)__builtin_alloca(n);
  char *b = (char *)__builtin_alloca(4);
  char *p = b + 3;
  if (!(p > b)) reach_error();
  char *r = __VERIFIER_nondet_int() ? p : b;
  if (r != p && r != b) reach_error();
  (void)a;
  return 0;
}
