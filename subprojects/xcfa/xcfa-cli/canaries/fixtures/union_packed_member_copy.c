// A struct copied into and out of a union member stored as bits of the union's word. The copy used
// to take the word as a base address; under integer arithmetic that silently touched another object.
extern void abort(void);
void reach_error() { abort(); }

struct S { unsigned int lo; unsigned int hi; };
union U { struct S s; unsigned long long q; };

int main() {
  union U u;
  struct S t, r;

  u.q = 0;
  t.lo = 5u; t.hi = 7u;
  u.s = t;                                        /* into the word */
  if (u.q != 30064771077ULL) reach_error();       /* (7 << 32) + 5 */
  t.lo = 9u;
  if (u.s.lo != 5u) reach_error();                /* a copy, not an alias */

  u.q = 8589934593ULL;                            /* lo = 1, hi = 2 */
  r = u.s;                                        /* out of the word */
  if (r.lo != 1u || r.hi != 2u) reach_error();
  return 0;
}
