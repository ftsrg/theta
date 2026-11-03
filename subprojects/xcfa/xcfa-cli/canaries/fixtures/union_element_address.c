// Under the cell models a union array element is a cell holding the union's own base, so `&m[1]`
// is that base, not the cell's address: writing through it used to overwrite the base cells.
extern void abort(void);
void reach_error(void) { abort(); }
union U { int a; char c[4]; };
union U m[3];
int main(void) {
  union U *p = &m[1];
  p->a = 7;
  union U *q = &m[2];
  q->a = 9;
  if (m[1].a != 7 || m[2].a != 9 || m[0].a != 0) reach_error();
  return 0;
}
