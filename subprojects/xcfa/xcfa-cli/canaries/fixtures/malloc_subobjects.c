// Under the multi model a nested struct or array member of a malloc'd struct is an object of its
// own, whose base is held in a cell of the block. The block allocates one per element, as a stack
// object does; unallocated, the cell is unconstrained and the writes below can land anywhere.
#include <stdlib.h>
extern void abort(void);
void reach_error(void) { abort(); }

struct in {
  int x;
  int y;
};
struct outer {
  int v;
  struct in a;
  int arr[3];
};

int main(void) {
  struct outer *o = malloc(2 * sizeof(struct outer));
  if (!o) return 0;
  o[0].v = 1;
  o[1].v = 2;
  o[0].a.x = 3;
  o[1].a.x = 4;
  o[0].arr[2] = 5;
  o[1].arr[2] = 6;
  if (o[0].v != 1 || o[1].v != 2) reach_error();
  if (o[0].a.x != 3 || o[1].a.x != 4) reach_error();
  if (o[0].arr[2] != 5 || o[1].arr[2] != 6) reach_error();
  free(o);
  return 0;
}
