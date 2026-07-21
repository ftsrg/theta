// batch 54: `unsigned char` values under bitvector arithmetic.
// CComplexType.getType matches a bitvector's width against the architecture's type sizes and
// switches on the name -- but had no `case "char"`, and `char` is the first entry whose width is 8.
// So every (Bv 8) fell out of the switch and threw "No suitable width found for type: (Bv 8)",
// with no initializer or bitfield needed to trigger it. Three ldv-linux tasks reached it through a
// portfolio configuration in the 2026-07-20 run and regressed from correct to frontend-failed.
struct A {
  unsigned char a;
  unsigned char b : 2;
  unsigned char c : 2;
  unsigned char d : 4;
};
struct A g = {.b = 3};
struct A h;

unsigned char plain = 200;

int main() {
  h.a = 1;
  h.b = 2;
  h.d = 9;
  plain = plain + 1;
  return (g.b != 3) + (h.a != 1) + (h.b != 2) + (h.d != 9) + (plain != 201);
}
