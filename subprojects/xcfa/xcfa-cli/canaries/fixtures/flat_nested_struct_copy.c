// Copying a struct with an inline struct member copies the member's cells by value: the copy
// and the original stay independent, and so does a member copied out on its own.
extern void abort(void);
void reach_error() { abort(); }

struct in { int x; int y; };
struct out { int a; struct in in; };

int main(void) {
  struct out a, b;
  a.a = 0;
  a.in.x = 1;
  a.in.y = 2;
  b = a;
  if (b.in.x != 1 || b.in.y != 2) reach_error();
  b.in.x = 3;
  if (a.in.x != 1) reach_error();
  struct in c = a.in;
  c.y = 9;
  if (a.in.y != 2) reach_error();
  return 0;
}
