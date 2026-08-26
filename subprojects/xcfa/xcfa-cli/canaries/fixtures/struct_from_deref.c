// batch 41: struct s = *p / = o.field copies out of a cell
struct S { int a; int b; };
int main() {
  struct S s; s.a = 1;
  struct S *p = &s;
  struct S t = *p;
  return t.a != 1;
}
