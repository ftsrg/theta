// A block of size 0 that malloc returns non-null is live and may be freed (C17 7.22.3).
extern int __VERIFIER_nondet_int(void);
void *malloc(unsigned long);
void free(void *);

int main(void) {
  int n = __VERIFIER_nondet_int();
  if (n < 0 || n > 100000) return 0;
  int *p = malloc(n * sizeof(int));
  if (!p) return 0;
  if (n > 0) p[n - 1] = 1;
  free(p);
  return 0;
}
