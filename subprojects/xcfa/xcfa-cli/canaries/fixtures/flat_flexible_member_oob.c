// A flexible array member malloc'd with room for two elements: under flat the recorded size is the
// header's cells plus two elements', so indexing the third is out of bounds.
void *malloc(unsigned long);
void free(void *);

struct s { int n; int d[]; };

int main(void) {
  struct s *p = malloc(sizeof(struct s) + 2 * sizeof(int));
  if (!p) return 0;
  p->d[1] = 1;
  p->d[2] = 2;
  free(p);
  return 0;
}
