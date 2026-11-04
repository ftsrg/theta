// calloc bound only through `void *` is still zeroed, not silently lowered to malloc.
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "calloc_void_binding.c", 3, "reach_error"); }
extern void *calloc(unsigned long, unsigned long);
int main() {
  void *q = calloc(4, sizeof(int));
  if (!q) return 0;
  int *p = q;
  p[1] = 5;
  if (p[2] != 0 || p[1] != 5) reach_error();
  return 0;
}
