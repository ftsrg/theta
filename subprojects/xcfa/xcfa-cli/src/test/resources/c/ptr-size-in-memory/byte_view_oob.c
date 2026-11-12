extern void *malloc(unsigned long);
extern void free(void *);
extern int __VERIFIER_nondet_int(void);
int main(void) {
  unsigned int *p = malloc(sizeof(unsigned int));
  if (!p) return 0;
  *p = 0x01020304u;
  unsigned char c = ((unsigned char *)p)[4];
  free(p);
  return c;
}
