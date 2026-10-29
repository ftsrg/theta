// Under the bytes model every initializer value lands at its real byte offset: array elements at
// i * sizeof, struct members at offsetof, nested aggregates inline, and what the braces leave out
// is zero -- for globals, locals, and the zero-initialized global alike.
extern void abort(void);
void reach_error() { abort(); }

struct in { char c; int k; long l; };
struct out { short h; struct in n; int a[2]; };

int g[3] = {1, 2, 3};
struct out go = {1, {2, 3, 4}, {5, 6}};
struct out gz;

int main(void) {
  struct out lo = {7, {8, 9}, {10}};
  long la[2] = {11, 12};
  if (g[1] != 2 || g[2] != 3) reach_error();
  if (go.h != 1 || go.n.c != 2 || go.n.k != 3 || go.n.l != 4 || go.a[1] != 6) reach_error();
  if (gz.n.k != 0 || gz.n.l != 0 || gz.a[1] != 0) reach_error();
  if (lo.h != 7 || lo.n.c != 8 || lo.n.k != 9 || lo.n.l != 0 || lo.a[0] != 10 || lo.a[1] != 0)
    reach_error();
  if (la[1] != 12) reach_error();
  return 0;
}
