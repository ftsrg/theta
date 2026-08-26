// C completes the declarator at the `=`, so the name being declared is already in scope
// inside its own initializer. The frontend registered it only *afterwards*, so both of the
// shapes below died with "No such variable or macro" -- and that message was **46% of all
// before-parsing frontend failures** in run 84, because `p = malloc(sizeof *p)` is how the
// heap/memsafety families allocate and the self-linked form is how the Linux kernel writes
// every statically initialised lock and list head.
#include <stdlib.h>
extern void abort(void);
void reach_error() { abort(); }

struct node {
  struct node *next;
  int v;
};

static struct node sentinel = {&sentinel, 7}; // initializer names the variable itself

int main() {
  struct node *p = malloc(sizeof *p); // size mentions p
  if (!p) return 0;
  p->v = 1;
  if (sentinel.next != &sentinel || sentinel.v != 7) reach_error();
  if (p->v != 1) reach_error();
  free(p);
  return 0;
}
