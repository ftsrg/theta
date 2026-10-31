// A struct member declared through an array typedef is that array, not a single cell; otherwise
// `s.head[1]` and `s.tail` share storage and the check below fails.
extern void abort(void);
void reach_error(void) { abort(); }

typedef int pair_t[2];
struct S {
  pair_t head;
  int tail;
};

int main(void) {
  struct S s;
  s.head[1] = 5;
  s.tail = 1;
  if (s.head[1] != 5) reach_error();
  return 0;
}
