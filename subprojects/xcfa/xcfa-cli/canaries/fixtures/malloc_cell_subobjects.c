// A block whose pointer is stored straight into a struct field (`h->nx = malloc(...)`) is typed by
// that field, so it gets its sub-objects too rather than being treated as untyped.
#include <stdlib.h>
extern void abort(void);
void reach_error(void) { abort(); }

struct in {
  int x;
  int y;
};
struct node {
  int v;
  struct in a;
  struct node *nx;
};

int main(void) {
  struct node *h = malloc(sizeof *h);
  if (!h) return 0;
  h->nx = malloc(sizeof(struct node));
  if (!h->nx) return 0;
  h->nx->v = 2;
  h->nx->a.x = 5;
  if (h->nx->v != 2) reach_error();
  return 0;
}
