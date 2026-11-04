// An array of structs as an inline struct member, indexed by a nondet value: element `i` is
// found at the member's offset plus `i` element strides, never on the parent's other members.
extern void abort(void);
void reach_error() { abort(); }
extern int __VERIFIER_nondet_int(void);

struct p { int x; int y; };
struct s { int n; struct p pts[2]; int tail; };

int main(void) {
  struct s v;
  v.n = 1;
  v.tail = 7;
  v.pts[0].x = 0;
  v.pts[0].y = 0;
  int i = __VERIFIER_nondet_int();
  if (i < 0 || i > 1) return 0;
  v.pts[i].y = 3;
  v.pts[1].x = 4;
  if (v.tail != 7 || v.n != 1) reach_error();
  if (v.pts[i].y != 3) reach_error();
  return 0;
}
