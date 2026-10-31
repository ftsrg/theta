// A loop of in-bounds accesses through the pointer malloc returned: under flat addressing each one
// is checked against its block directly, not through a slot witness the solver has to find. With
// the witness alone this times out; it is a guard on the check's cost, not only its verdict.
void *malloc(unsigned long);
void *realloc(void *, unsigned long);
void free(void *);

int main(void) {
  int *p = malloc(2 * sizeof(int));
  if (!p) return 0;
  int *q = malloc(2 * sizeof(int));
  if (!q) return 0;
  q[0] = 7;
  int *r = realloc(p, 16 * sizeof(int));
  if (!r) return 0;
  for (int i = 0; i < 16; i++) r[i] = 1;
  free(r);
  free(q);
  return 0;
}
