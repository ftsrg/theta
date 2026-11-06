// A VLA whose size exceeds PTRDIFF_MAX bytes (GCC's maximum object size) is undefined: an
// unsigned length times sizeof(int) can exceed it in ILP32.
extern unsigned int __VERIFIER_nondet_uint(void);

int main() {
  unsigned int n = __VERIFIER_nondet_uint();
  int a[n];
  return 0;
}
