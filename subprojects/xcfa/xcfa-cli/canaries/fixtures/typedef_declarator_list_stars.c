// Each declarator of a list carries its own stars: `PP` below is a pointer to the struct and `PPP`
// a pointer to that, while `P` has none. `PP` used to name the struct itself, so `r->v` failed
// with "Only pointers expected here".
extern void abort(void);
void reach_error() { abort(); }

typedef struct P { int x; int v; int w; } P, *PP, **PPP;

int main() {
  P s;
  PP r = &s;
  PPP rr = &r;
  int g = 0, *gp = &g;
  r->v = 1;
  (*rr)->x = 2;
  *gp = 3;
  if (s.v != 1 || s.x != 2 || g != 3) reach_error();
  if (sizeof(PP) != sizeof(void *) || sizeof(*r) != sizeof(P)) reach_error();
  return 0;
}
