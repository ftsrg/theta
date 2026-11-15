// An element count whose product with the element size does not fit in size_t describes no object:
// calloc returns NULL rather than a block of the wrapped-around size, which holds no element.
extern unsigned int __VERIFIER_nondet_uint(void);
extern void *calloc(unsigned int, unsigned int);
extern void abort(void);
void reach_error(void) { abort(); }
int main(void) {
  unsigned int n = __VERIFIER_nondet_uint();
  int *p = (int *)calloc(n, sizeof(int));
  if (p == 0) return 0;
  if (n > 0 && p[0] != 0) reach_error();
  return 0;
}
