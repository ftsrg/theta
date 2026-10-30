// GNU C allows a zero-length array; only accessing it is undefined. A VLA sized from a nondet
// that may be 0 and is never accessed must not be flagged.
extern unsigned int __VERIFIER_nondet_uint(void);

int main() {
  unsigned int n = __VERIFIER_nondet_uint();
  if (n > 1000) return 0;
  int a[n]; // n may be 0
  return 0;
}
