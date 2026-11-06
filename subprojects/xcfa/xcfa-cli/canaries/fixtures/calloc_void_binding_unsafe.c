// The zero fill of a calloc bound through `void *` is real: p[1] == 0 is reachable.
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "calloc_void_binding_unsafe.c", 3, "reach_error"); }
extern void *calloc(unsigned long, unsigned long);
int main() {
  void *q = calloc(2, sizeof(int));
  if (!q) return 0;
  int *p = q;
  if (p[1] == 0) reach_error();
  return 0;
}
