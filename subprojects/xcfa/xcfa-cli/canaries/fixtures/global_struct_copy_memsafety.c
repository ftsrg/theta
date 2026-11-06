// Copying a struct, by assignment or by value as an argument, goes through its nested struct
// members, so global initialization has to allocate them although no member access names them.
struct A { int x; int y; };
struct S { struct A a; };
struct T { int status; struct S lock; };
struct T g1 = {1, {{1, 2}}};
struct T g2 = {2, {{3, 4}}};
int f(struct S s) { return 0; }
int main() {
  g1.lock = g2.lock;
  return f(g1.lock);
}
