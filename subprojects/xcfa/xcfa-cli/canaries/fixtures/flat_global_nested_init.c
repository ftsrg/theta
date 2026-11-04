// A global's initializer writes the nested member's values into the parent's own cells, at
// the member's inline offset, and a pointer to the member reads them back from there.
extern void abort(void);
void reach_error() { abort(); }

struct in { int x; int y; };
struct out { int a; struct in in; };
struct out g = {1, {2, 3}};

int main(void) {
  struct in *p = &g.in;
  if (p->y != 3 || g.a != 1) reach_error();
  p->x = 9;
  if (g.in.x != 9) reach_error();
  return 0;
}
