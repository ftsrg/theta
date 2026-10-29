// A struct with a flexible array member, allocated with room for three elements: indexing the
// member inside that room is valid.
void *malloc(unsigned long);
void free(void *);

struct s { int n; int d[]; };

int main(void) {
  struct s *p = malloc(sizeof(struct s) + 3 * sizeof(int));
  if (!p) return 0;
  p->n = 3;
  p->d[2] = 1;
  free(p);
  return 0;
}
