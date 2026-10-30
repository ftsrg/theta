// An out-of-bounds write on a block of symbolic size is caught: the recorded size is the
// element count the byte size covers, not the byte count itself.
extern int __VERIFIER_nondet_int(void);
void *malloc(unsigned long);
void free(void *);

int main(void) {
  int n = __VERIFIER_nondet_int();
  if (n <= 0 || n > 100000) return 0;
  int *p = malloc(n * sizeof(int));
  if (!p) return 0;
  p[n] = 1;
  free(p);
  return 0;
}
