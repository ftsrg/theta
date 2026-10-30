// A local's brace initializer under inline layout: nested braces fill the member's cells in
// place, and a partial initializer zero-fills every cell it leaves out, the nested member's
// included (C11 6.7.9p21).
extern void abort(void);
void reach_error() { abort(); }

struct in { int x; int y; };
struct out { int a; struct in in; int b; };

int main(void) {
  struct out o = {1, {2, 3}, 4};
  struct in *p = &o.in;
  if (o.a != 1 || p->x != 2 || p->y != 3 || o.b != 4) reach_error();
  struct out z = {5};
  if (z.in.x != 0 || z.in.y != 0 || z.b != 0) reach_error();
  return 0;
}
