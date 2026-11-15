// As flat_pointer_past_object.c, with an index only the analysis knows: some k reach `b`.
extern int __VERIFIER_nondet_int(void);
int a[3], b[3];

int main(void) {
  int k = __VERIFIER_nondet_int();
  if (k < 0 || k > 4) return 0;
  int *p = a;
  return p[k];
}
