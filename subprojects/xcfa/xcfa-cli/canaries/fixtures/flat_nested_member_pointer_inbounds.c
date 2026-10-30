// A pointer to a field of an inline struct member is in bounds of the enclosing allocation:
// the valid-deref check finds the object containing the address, not a sub-object of its own.
void *malloc(unsigned long);
void free(void *);

struct in { int x; int y; };
struct out { int a; struct in in; int b; };

int main(void) {
  struct out *o = malloc(sizeof(*o));
  if (!o) return 0;
  int *py = &o->in.y;
  *py = 1;
  o->b = 2;
  free(o);
  return 0;
}
