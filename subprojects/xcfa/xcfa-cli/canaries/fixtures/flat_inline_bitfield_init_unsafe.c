// The reachable twin of flat_inline_bitfield_init.c: the initialized bitfield values really are
// read back, so an initializer that lost them (leaving zeros) would hide this error.
extern void abort(void);
void reach_error() { abort(); }

struct flags {
  unsigned a : 3;
  unsigned b : 5;
  int c;
};

struct outer {
  int head;
  struct flags f;
  struct flags g[2];
};

struct outer gl = {1, {5, 17, 3}, {{1, 2, 3}, {7, 31, -4}}};

int main(void) {
  if (gl.g[1].a == 7 && gl.g[1].b == 31) reach_error();
  return 0;
}
