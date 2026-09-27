// A struct nested in a packed union member is more bits of the union's word, not an object with a
// base address: read, copied and written through that word. `union R` is the anonymous nested
// bitfield group of register overlays; `union W` nests a struct wider than an ILP32 pointer.
extern void abort(void);
void reach_error() { abort(); }

struct In { unsigned char a; unsigned char b; };
struct Out { struct In i; unsigned short c; };
union UO { struct Out o; unsigned int raw; };

union R {
  unsigned int raw;
  struct { struct { unsigned int a : 4; unsigned int b : 4; }; unsigned int c : 24; };
};

struct Pair { unsigned int lo; unsigned int hi; };
struct Wrap { struct Pair p; };
union W { struct Wrap w; unsigned long long q; };

int main() {
  union UO uo; struct In x, y;
  uo.raw = 197121u;                               /* a = 1, b = 2, c = 3 */
  x = uo.o.i;                                     /* out of the word */
  if (x.a != 1 || x.b != 2) reach_error();
  y.a = 7; y.b = 8;
  uo.o.i = y;                                     /* into it */
  if (uo.raw != 198663u) reach_error();           /* 7 + 8*256 + 3*65536 */
  uo.o.i.a = 9;                                   /* a field of it */
  if (uo.raw != 198665u || uo.o.i.b != 8) reach_error();

  union R r;
  r.raw = 291u;                                   /* 0x123: a = 3, b = 2, c = 1 */
  if (r.a != 3u || r.b != 2u || r.c != 1u) reach_error();
  r.b = 5u;
  if (r.raw != 339u) reach_error();               /* 0x153 */

  union W w; struct Pair p, p2;
  w.q = 8589934593ULL;                            /* lo = 1, hi = 2 */
  p = w.w.p;
  if (p.lo != 1u || p.hi != 2u) reach_error();
  p2.lo = 3u; p2.hi = 4u;
  w.w.p = p2;
  if (w.q != 17179869187ULL) reach_error();       /* (4 << 32) + 3 */
  return 0;
}
