// A struct copy under the bytes model copies every byte cell of the layout, nested members
// included, rather than one cell per member index.
extern void abort(void);
void reach_error() { abort(); }

struct in { int a; long b; };
struct out { int h; struct in n; };

int main(void) {
  struct in i = {1, 2};
  struct in j = i;
  struct out o;
  o.h = 3;
  o.n = i;
  if (j.a != 1 || j.b != 2 || o.h != 3 || o.n.a != 1 || o.n.b != 2) reach_error();
  return 0;
}
