// A failed realloc returns NULL and leaves the old block as it was.
extern void abort(void);
void reach_error() { abort(); }
extern void *malloc(unsigned long);
extern void *realloc(void *, unsigned long);
extern void free(void *);

int main() {
  int *p = (int *)malloc(sizeof(int));
  if (!p) return 0;
  *p = 5;
  int *q = (int *)realloc(p, 2 * sizeof(int));
  if (!q) {
    if (*p != 5) reach_error();
    free(p);
    return 0;
  }
  free(q);
  return 0;
}
