// memset zeroes every byte of the struct, also the ones a byte view reads inside a field.
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "fixture.c", 1, "reach_error"); }
void __VERIFIER_assert(_Bool cond) { if (!cond) { reach_error(); abort(); } }
extern void *memset(void *, int, unsigned long);

struct node {
  struct node *next;
  struct node *prev;
};

int main(void) {
  struct node n;
  memset(&n, 0, sizeof(n));
  const unsigned char *bytes = (const unsigned char *)&n;
  __VERIFIER_assert(bytes[5] == 0);
  return 0;
}
