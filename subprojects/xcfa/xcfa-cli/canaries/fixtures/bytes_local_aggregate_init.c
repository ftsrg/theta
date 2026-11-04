// Under the bytes model a local brace initializer lands at the real byte offsets, and what the
// braces leave out is zero.
// One object per fixture: under bytes, verification time grows quickly with the number of objects.
extern void abort(void);
void reach_error() { abort(); }

struct in { char c; int k; long l; };
struct out { short h; struct in n; int a[2]; };

int main(void) {
  struct out lo = {7, {8, 9}, {10}};
  if (lo.h != 7 || lo.n.c != 8 || lo.n.k != 9 || lo.n.l != 0 || lo.a[0] != 10 || lo.a[1] != 0)
    reach_error();
  return 0;
}
