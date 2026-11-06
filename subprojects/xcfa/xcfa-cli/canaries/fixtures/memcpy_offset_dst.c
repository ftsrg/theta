// A mem* call on `a + 1` keeps the offset: the cell-per-value models fold it into the index.
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "memcpy_offset_dst.c", 3, "reach_error"); }
extern void *memcpy(void *, const void *, unsigned long);
int main() {
  char a[4] = {1, 2, 3, 4};
  char b[3] = {7, 8, 9};
  memcpy(a + 1, b, 3);
  if (a[0] != 1 || a[1] != 7 || a[3] != 9) reach_error();
  return 0;
}
