extern void *malloc(unsigned long);
extern void free(void *);
extern int __VERIFIER_nondet_int(void);
int main(void) {
  unsigned char *p = malloc(4);
  if (!p) return 0;
  int x = p[4];
  free(p);
  return x;
}
