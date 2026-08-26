// batch 56: union members of differing widths/signedness share the word as bit slices.
// A union's members all start at offset 0, so a narrower member is the low bits of the same word.
// This used to be refused as "members do not all share a representation" -- the single largest
// addressable frontend cluster (~1,029 tasks in the 2026-07-20 run). Values are checked by the
// analysis (u.raw = 2^32+1 => u.half == 1 proves Safe; negating it proves Unsafe); this fixture
// guards that the shapes still reach the frontend at all.
union Widths {
  unsigned long raw;
  unsigned int half;
};
union Signs {
  int s;
  unsigned u;
};
union Narrow {
  int i;
  char c;
};
union PtrIdiom {
  void *ptr;
  unsigned long i;
};

union Widths w;
union Signs g;
union Narrow n;
union PtrIdiom p;

int main() {
  int local = 5;
  w.raw = 0;
  w.half = 7;
  g.u = 1;
  n.i = 300;
  p.ptr = &local;
  return (w.raw != 7) + (g.s != 1) + (n.c != 44) + (p.i == 0);
}
