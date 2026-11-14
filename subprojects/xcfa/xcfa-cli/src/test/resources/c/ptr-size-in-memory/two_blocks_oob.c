extern void *malloc(unsigned long);
extern void free(void *);
extern int __VERIFIER_nondet_int(void);
int main(void) {
  unsigned char *p = malloc(2);
  unsigned char *q = malloc(8);
  int x = 0;
  if (p && q) x = p[__VERIFIER_nondet_int() ? 1 : 2];  // p[2]: one past p (not into q: theta#810)
  free(p);
  free(q);
  return x;
}
