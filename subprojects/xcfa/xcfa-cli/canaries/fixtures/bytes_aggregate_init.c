// Under the bytes model every initializer value lands at its real byte offset: struct members at
// offsetof and nested aggregates inline, with what the braces leave out zero.
// One object per fixture: under bytes, verification time grows quickly with the number of objects.
extern void abort(void);
void reach_error() { abort(); }

struct in { char c; int k; long l; };
struct out { short h; struct in n; int a[2]; };

struct out go = {1, {2, 3, 4}, {5, 6}};

int main(void) {
  if (go.h != 1 || go.n.c != 2 || go.n.k != 3 || go.n.l != 4 || go.a[1] != 6) reach_error();
  return 0;
}
