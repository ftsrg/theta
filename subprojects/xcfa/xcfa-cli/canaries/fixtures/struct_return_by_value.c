// A struct returned by value is a copy: the caller reads it after the callee's locals are dead.
struct S {
  long a;
  long b;
};

struct S make(long v) {
  struct S s;
  s.a = v;
  s.b = v + 1;
  return s;
}

int main(void) {
  struct S r = make(1);
  struct S q = make(5);
  return r.b == 2 && q.a == 5 ? 0 : 1;
}
