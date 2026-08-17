// The other side of vla_zero_length.c: once the length is known positive there is no
// violation, and the check attached to the allocation must not invent one. Also pins that a
// constant-sized array never pays for the check at all.
extern unsigned int __VERIFIER_nondet_uint(void);

int main() {
  unsigned int n = __VERIFIER_nondet_uint();
  if (n < 1 || n > 8) return 0;
  int a[n];
  int fixed[4];
  a[0] = 1;
  fixed[3] = 2;
  return a[0] + fixed[3];
}
