// A struct of members with different widths is one cell per member under the flat model, so
// its recorded size is its member count, and writing its last member stays in bounds.
void *malloc(unsigned long);
void free(void *);

struct m { char c; long l; short s; };

int main(void) {
  struct m *p = malloc(sizeof(struct m));
  if (!p) return 0;
  p->c = 1;
  p->l = 2;
  p->s = 3;
  free(p);
  return 0;
}
