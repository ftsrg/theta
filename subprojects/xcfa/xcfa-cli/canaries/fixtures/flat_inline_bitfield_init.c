// A struct with packed bitfields, nested in another struct (alone and as array elements), is laid
// out inline under flat: bitfields sharing a storage unit share one cell, and a static
// initializer folds their values into it. A later store to one bitfield keeps its neighbour.
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
  int tail;
};

struct outer gl = {1, {5, 17, 3}, {{1, 2, 3}, {7, 31, -4}}, 9};

int main(void) {
  if (gl.head != 1 || gl.f.a != 5 || gl.f.b != 17 || gl.f.c != 3) reach_error();
  if (gl.g[0].b != 2 || gl.g[1].a != 7 || gl.g[1].b != 31 || gl.g[1].c != -4) reach_error();
  if (gl.tail != 9) reach_error();
  gl.f.b = 2;
  if (gl.f.a != 5 || gl.f.b != 2 || gl.f.c != 3) reach_error();
  return 0;
}
