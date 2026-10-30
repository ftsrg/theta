// Under the flat model a struct member of a struct is laid out inline, so `&o->in` is the
// address of the parent's own cells, not a separate object whose base is kept in a cell. A
// malloc'd struct never initialized that base cell, so writes through `&o->in` went to an
// arbitrary object and reads of `o->in.y` disagreed with them.
extern void abort(void);
void reach_error() { abort(); }
void *malloc(unsigned long);

struct in { int x; int y; };
struct out { int a; struct in in; };

int main(void) {
  struct out *o = malloc(sizeof(*o));
  if (!o) return 0;
  struct in *pi = &o->in;
  int *py = &pi->y;
  *py = 5;
  o->a = 1;
  pi->x = 2;
  if (o->in.y != 5 || o->a != 1 || o->in.x != 2) reach_error();
  return 0;
}
