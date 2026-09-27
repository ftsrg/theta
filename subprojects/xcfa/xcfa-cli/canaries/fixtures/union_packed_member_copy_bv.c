// Copies into and out of packed union members under bitvector arithmetic, where a word narrower
// than a pointer used to crash the copy; also a slice of the word, bitfields, nesting, signed
// fields, word to word and a by-value argument.
extern void abort(void);
void reach_error() { abort(); }

struct T { unsigned short head; unsigned short tail; };
union Lock { unsigned int ht; struct T t; };
struct L { union Lock u; };

struct H { unsigned short a; unsigned short b; };
union V { struct H h; unsigned long long q; };   /* h is only the low half of the word */

struct B { unsigned int x : 4; unsigned int y : 12; unsigned int z : 16; };
union UB { struct B b; unsigned int raw; };

struct In { unsigned char a; unsigned char b; };
struct Out { struct In i; unsigned short c; };
union UO { struct Out o; unsigned int raw; };

struct N { int lo; int hi; };
union UN { struct N n; unsigned long long q; };

int lo_of(struct N n) { return n.lo; }

int is_locked(struct L *l) {
  struct T tmp;
  tmp = l->u.t;
  return tmp.tail != tmp.head;
}

int main() {
  struct L l;
  l.u.ht = 196611u;                               /* head = 3, tail = 3 */
  if (is_locked(&l)) reach_error();
  l.u.ht = 196612u;                               /* head = 4, tail = 3 */
  if (!is_locked(&l)) reach_error();

  union V v; struct H x, y;
  v.q = 18446744069414584320ULL;                  /* 0xFFFFFFFF00000000 */
  x.a = 1; x.b = 2;
  v.h = x;                                        /* a slice: the high half must survive */
  if (v.q != 18446744069414715393ULL) reach_error();   /* 0xFFFFFFFF00020001 */
  y = v.h;
  if (y.a != 1 || y.b != 2) reach_error();

  union UB ub; struct B b, b2;
  b.x = 3; b.y = 100; b.z = 7;
  ub.b = b;
  if (ub.raw != 460355u) reach_error();           /* 3 + 100*16 + 7*65536 */
  ub.raw = 131105u;                               /* x = 1, y = 2, z = 2 */
  b2 = ub.b;
  if (b2.x != 1 || b2.y != 2 || b2.z != 2) reach_error();

  union UO uo; struct Out o, o2;
  o.i.a = 1; o.i.b = 2; o.c = 3;
  uo.o = o;
  if (uo.raw != 197121u) reach_error();           /* 1 + 2*256 + 3*65536 */
  o2 = uo.o;
  if (o2.i.a != 1 || o2.i.b != 2 || o2.c != 3) reach_error();

  union UN un, vn; struct N n;
  n.lo = -5; n.hi = -1;
  un.n = n;
  vn.n = un.n;
  if (vn.n.lo != -5 || vn.n.hi != -1) reach_error();
  if (lo_of(vn.n) != -5) reach_error();
  return 0;
}
