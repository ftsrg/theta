// A struct-valued expression initializing an inline member (`{1, c, 7}`) copies all of the
// member's cells. The zero fill must then treat every one of them as written: marking only the
// first cell zeroed `o.in.y` right after it was copied.
extern void abort(void);
void reach_error() { abort(); }

struct in { int x; int y; };
struct out { int a; struct in in; int b; };

int main(void) {
  struct in c = {5, 6};
  struct out o = {1, c, 7};
  c.x = 0;
  if (o.in.x != 5 || o.in.y != 6 || o.b != 7 || o.a != 1) reach_error();
  return 0;
}
