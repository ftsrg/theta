// The block comes from a wrapper, so where it is allocated its type is unknown and its sub-objects
// cannot be: the multi model hands the program to flat, which lays the members out inline.
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

void *xmalloc(unsigned long n) {
  void *p = malloc(n);
  if (!p) abort();
  return p;
}

int main(void) {
  struct outer *o = xmalloc(sizeof *o);
  o->v = 1;
  o->a.x = 2;
  if (o->v != 1) reach_error();
  return 0;
}
