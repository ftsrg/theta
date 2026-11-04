// A parameter or local shadows a typedef name, and `struct T *T` declares a variable named T.
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "typedef_shadowing.c", 3, "reach_error"); }
typedef struct table table;
struct table { int y; };
struct s { int x; };
int f(struct s *table) {
  table->x = 1;
  return table->x;
}
int g(void) {
  int table = 2;
  return table * 3;
}
int h(void) {
  table t;
  table *p = &t;
  p->y = 4;
  return t.y;
}
int k(void) {
  struct table *table;
  struct table x;
  table = &x;
  table->y = 1;
  return table->y;
}
int main() {
  struct s v;
  if (f(&v) != 1 || g() != 6 || h() != 4 || k() != 1) reach_error();
  return 0;
}
