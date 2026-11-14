extern void *malloc(unsigned long);
extern void free(void *);
extern int __VERIFIER_nondet_int(void);
int main(void) {
  int *p = malloc(sizeof(int));
  if (!p) return 0;
  *p = 1;
  free(p);
  return *p;
}
