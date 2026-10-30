// Union members of the struct elements of 2-D arrays, local and global, are objects of their own.
// A local array allocated them only in 1-D arrays, so in a 2-D one the members aliased.
extern void abort(void);
void reach_error() { abort(); }

union U {
  int i;
  char c[4];
};
struct S {
  int k;
  union U u;
};

struct S g[2][2];

int main(void) {
  struct S b[2][2];
  b[1][1].u.i = 5;
  b[0][1].u.i = 6;
  g[1][1].u.i = 7;
  if (b[1][1].u.i != 5 || g[1][1].u.i != 7 || g[0][1].u.i != 0) reach_error();
  return 0;
}
