// A one-past-the-end write on a malloc'd block is an invalid dereference even though the next
// allocation follows right after it: the gap after every object keeps the two apart.
void *malloc(unsigned long);
void free(void *);

int main(void) {
  int *p = malloc(2 * sizeof(int));
  int *q = malloc(2 * sizeof(int));
  if (!p || !q) return 0;
  p[2] = 1;
  free(p);
  free(q);
  return 0;
}
