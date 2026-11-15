extern void *malloc(unsigned long);
extern void free(void *);
extern int __VERIFIER_nondet_int(void);
int main(void) {
  unsigned char *p = malloc(2);
  unsigned char *q = malloc(8);
  int x = 0;
  if (p && q) {
    q[7] = 1;
    x = q[7] + p[1];
  }
  free(p);
  free(q);
  return x;
}
