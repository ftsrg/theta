// The two pointers lie in one object that straddles the sign boundary of the address width;
// their difference is small and cannot overflow.
extern int __VERIFIER_nondet_int(void);

int main() {
  int n = __VERIFIER_nondet_int();
  if (n < 1) n = 1;
  char *a = (char *)__builtin_alloca(n);
  char *b = (char *)__builtin_alloca(4);
  char *p = b + 3;
  long d = p - b;
  (void)a;
  return (int)d;
}
