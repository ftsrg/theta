// A local aggregate's initializer used to be written as flat cell offsets in the declared
// variable, as if nested aggregates were laid out inline. The object model does the
// opposite: a struct's struct- or array-typed field gets storage of its own and the parent
// keeps only its base id. So `struct Outer o = {{1,2}, 3};` emitted `o[0]=1; o[1]=2;
// o[1]=3` -- the first write destroying the base of `in`'s object, which every read of
// `o.in.x` then dereferences, and the last two colliding on `z`'s cell.
extern void abort(void);
void reach_error() { abort(); }

struct Inner {
  int x, y;
};
struct Outer {
  struct Inner in;
  int z;
};

int main() {
  struct Outer o = {{1, 2}, 3};
  struct Outer part = {.z = 9}; // `in` is untouched by the braces, so it is zero
  if (o.in.x != 1 || o.in.y != 2 || o.z != 3) reach_error();
  if (part.in.x != 0 || part.in.y != 0 || part.z != 9) reach_error();
  return 0;
}
