// Returning a struct by value copies it, but its address stored elsewhere still dies at return.
struct S {
  long a;
  long b;
};

struct S *kept;

struct S make(void) {
  struct S s;
  s.a = 1;
  s.b = 2;
  kept = &s;
  return s;
}

int main(void) {
  struct S r = make();
  return kept->b == r.b; // use-after-return through the kept address
}
