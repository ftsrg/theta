// A byte written through an address that was kept in an integer changes the long it overlaps.
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "integer_address_byte_view.c", 3, "reach_error"); }
void __VERIFIER_assert(_Bool cond) { if (!cond) { reach_error(); abort(); } }

void set_byte(void *object) {
  unsigned char *bytes = (unsigned char *)object;
  bytes[1] = 1;
}

int main(void) {
  unsigned long x = 0;
  unsigned long address = (unsigned long)&x;
  set_byte((void *)address);
  __VERIFIER_assert(x == 0);
  return 0;
}
