// The unsafe twin of union_packed_member_copy.c: the copy into the member used to miss it, and
// this reachable error was reported SAFE.
extern void abort(void);
void reach_error() { abort(); }

struct S { unsigned int lo; unsigned int hi; };
union U { struct S s; unsigned long long q; };

int main() {
  union U u;
  struct S t;
  u.q = 0;
  t.lo = 5u; t.hi = 7u;
  u.s = t;
  if (u.s.lo == 5u) reach_error();
  return 0;
}
