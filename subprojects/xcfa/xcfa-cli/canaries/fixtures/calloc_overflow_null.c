// An element count whose product with the element size does not fit in size_t describes no object:
// calloc returns NULL rather than a block of the wrapped-around size, which holds no element.
extern int __VERIFIER_nondet_int(void);
extern void *calloc(unsigned int, unsigned int);
extern void abort(void);
void reach_error(void) { abort(); }
int main(void) {
  unsigned int n = 0x40000000u; // n * sizeof(int) wraps to 0
  if (__VERIFIER_nondet_int()) n = 1;
  int *p = (int *)calloc(n, sizeof(int));
  if (p == 0) return 0;
  if (p[0] != 0) reach_error();
  return 0;
}
