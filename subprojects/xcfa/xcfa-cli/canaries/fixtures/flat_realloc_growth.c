// A block grown by realloc keeps its base under flat addressing, so it must not run into the
// block allocated after it.
void *malloc(unsigned long);
void *realloc(void *, unsigned long);
void free(void *);
extern void abort(void);
void reach_error() { abort(); }

int main(void) {
  int *p = malloc(2 * sizeof(int));
  if (!p) return 0;
  int *q = malloc(2 * sizeof(int));
  if (!q) return 0;
  q[0] = 7;
  int *r = realloc(p, 16 * sizeof(int));
  if (!r) return 0;
  r[9] = 1;
  r[15] = 1;
  if (q[0] != 7) reach_error();
  free(r);
  free(q);
  return 0;
}
