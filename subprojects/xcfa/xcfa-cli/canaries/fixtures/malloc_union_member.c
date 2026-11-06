// A union member stays an object of its own even under flat, so a malloc'd struct holding one has
// to allocate it; unallocated, the writes through it land on the struct's other members.
#include <stdlib.h>
extern void abort(void);
void reach_error(void) { abort(); }

union U {
  int i;
  unsigned int j;
};
struct S {
  int k;
  union U u;
  int t;
};

int main(void) {
  struct S *p = malloc(sizeof *p);
  if (!p) return 0;
  p->k = 1;
  p->u.i = 5;
  p->t = 7;
  if (p->k != 1 || p->u.i != 5 || p->t != 7) reach_error();
  free(p);
  return 0;
}
