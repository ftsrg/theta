// The counterpart of flat_member_pointer_alias.c: a write through a pointer to an inline
// struct member must be visible through the parent, so this reaches the error.
extern void abort(void);
void reach_error() { abort(); }
void *malloc(unsigned long);

struct in { int x; int y; };
struct out { int a; struct in in; };

int main(void) {
  struct out *o = malloc(sizeof(*o));
  if (!o) return 0;
  struct in *pi = &o->in;
  o->in.y = 0;
  pi->y = 5;
  if (o->in.y == 5) reach_error();
  return 0;
}
