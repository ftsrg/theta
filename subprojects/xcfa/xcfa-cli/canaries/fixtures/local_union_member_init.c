// Unions inside local aggregates are initialized like a local union: a union member of a struct
// from its own braces or to zero when the braces skip it, and the elements of an array of unions,
// each an object of its own.
extern void abort(void);
void reach_error() { abort(); }

union U {
  int i;
  char c[4];
};
struct S {
  int k;
  union U u;
  int z;
};

int main(void) {
  struct S s = {1, {.c = {5}}, 2};
  struct S t = {.z = 4};
  union U la[2] = {[1] = {.i = 9}};
  if (s.u.i != 5 || s.z != 2 || t.u.i != 0) reach_error();
  if (la[1].i != 9 || la[0].i != 0) reach_error();
  return 0;
}
