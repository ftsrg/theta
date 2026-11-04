// A global union's brace initializer is stored at the bit offsets its members are read from, over
// zero, and is visible through every member view: a nested struct, a designated array member, a
// negative scalar spanning all bytes, and the halves of a word-sliceable union.
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

union U list = {{1, 2}};
union U named = {.s = {3, 4}};
union U neg = {.al = -1};
union W wlist = {{1, 2}};

int main() {
  if (list.d.b != 2 || list.s[4] != 2 || list.s[1] != 0) reach_error();
  if (named.d.a != 0x0403) reach_error();
  if (neg.d.b != -1) reach_error();
  if (wlist.raw != 0x200000001UL) reach_error();
  return 0;
}
