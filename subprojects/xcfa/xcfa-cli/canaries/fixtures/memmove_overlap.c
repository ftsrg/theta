// memmove reads every source cell before writing: with overlapping a+1 / a, a forward copy is wrong.
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "memmove_overlap.c", 3, "reach_error"); }
extern void *memmove(void *, const void *, unsigned long);
int main() {
  char a[4] = {1, 2, 3, 4};
  memmove(a + 1, a, 3);
  if (a[1] != 1 || a[3] != 3) reach_error();
  return 0;
}
