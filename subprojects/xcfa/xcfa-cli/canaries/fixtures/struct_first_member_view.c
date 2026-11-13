// Under multi a nested aggregate member is a separate object whose base sits in its parent's
// first cell, so a cast to a pointer to the first member must not read that cell as the member.
extern void abort(void);
void reach_error() {}
struct base { int tag; int y; };
struct derived { struct base b; int x; };
struct derived D;
int main() {
  D.b.tag = 3;
  struct base *p = (struct base *)&D;
  if (p->tag != 3) { reach_error(); abort(); }
  return 0;
}
