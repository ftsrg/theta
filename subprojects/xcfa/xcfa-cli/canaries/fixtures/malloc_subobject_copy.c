// A struct copy into a malloc'd block copies into its sub-objects, so they must exist; the copy
// must not share them with the source either.
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
};

int main(void) {
  struct outer *o = malloc(sizeof *o);
  if (!o) return 0;
  struct outer s;
  s.v = 7;
  s.a.x = 8;
  s.a.y = 9;
  *o = s;
  o->a.x = 1;
  if (s.a.x != 8 || o->v != 7 || o->a.y != 9) reach_error();
  free(o);
  return 0;
}
