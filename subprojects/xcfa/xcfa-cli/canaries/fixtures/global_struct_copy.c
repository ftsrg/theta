// A whole-struct copy reads every member, nested ones included, so global initialization has to
// write them although no member access names them.
extern void abort(void);
void reach_error() { abort(); }
struct A { int x; int y; };
struct S { struct A a; int z; };
struct S g1 = {{1, 2}, 3};
struct S g2 = {{3, 4}, 5};
struct S h;
int main() {
  g1 = g2;
  h = g1;
  if (h.z != 5) reach_error();
  return 0;
}
