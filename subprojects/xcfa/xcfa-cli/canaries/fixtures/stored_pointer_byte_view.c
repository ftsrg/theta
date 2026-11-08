// The byte view reaches the long through a pointer stored in a struct field.
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "stored_pointer_byte_view.c", 3, "reach_error"); }
void __VERIFIER_assert(_Bool cond) { if (!cond) { reach_error(); abort(); } }

struct holder {
  unsigned char *buffer;
};

int main(void) {
  unsigned long x = 0;
  struct holder h;
  h.buffer = (unsigned char *)(void *)&x;
  h.buffer[1] = 1;
  __VERIFIER_assert(x == 0);
  return 0;
}
