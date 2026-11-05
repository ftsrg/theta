// The backward memmove is exact: a[2] is the old a[1], so this error is reachable. A forward
// copy would overwrite a[1] first and give a[2] == 1.
extern unsigned int __VERIFIER_nondet_uint(void);
extern void *memmove(void *dst, const void *src, unsigned long n);
extern void abort(void);
void reach_error() { abort(); }

int main() {
  int a[3] = {1, 2, 3};
  unsigned int k = __VERIFIER_nondet_uint();
  if (k != 2) return 0;
  memmove(a + 1, a, k * sizeof(int));
  if (a[2] == 2) reach_error();
  return 0;
}
