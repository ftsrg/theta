// A global union without an initializer is zero in the cells its members are read from: the byte
// cells of a byte-laid-out union (one with an array member), the one word of a word-sliceable one.
// Its first member being a struct must not put that struct's base id into the storage.
extern void abort(void);
void reach_error() { abort(); }

struct S {
  int a;
  int b;
};
union U {
  struct S d;
  char s[8];
  long al;
};
union W {
  struct {
    unsigned int lo;
    unsigned int hi;
  } p;
  unsigned long raw;
};
struct O {
  int x;
  union U u;
};

union U zero;
union W wzero;
struct O outer;

int main() {
  if (zero.d.a != 0 || zero.s[5] != 0 || zero.al != 0) reach_error();
  if (wzero.raw != 0) reach_error();
  if (outer.u.d.b != 0) reach_error();
  return 0;
}
