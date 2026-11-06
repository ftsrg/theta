// A cycle through a by-value member (A holds a B, B points back to A) re-entered the inner B while
// it was still being expanded, so `p.b.a->b.a->x` found an `int` where B should be.
extern void abort(void);
void reach_error() { abort(); }

struct A {
  struct B {
    struct A *a;
    int y;
  } b;
  int x;
};

int main() {
  struct A p, q;
  p.b.a = &q;
  q.b.a = &p;
  p.x = 5;
  q.x = 6;
  if (p.b.a->b.a->x != 5 || p.b.a->x != 6) reach_error();
  return 0;
}
