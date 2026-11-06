// memset of a struct whose layout the cell-per-value models cannot state is retried under bytes.
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "memset_struct_nested_array.c", 3, "reach_error"); }
extern void *memset(void *, int, unsigned long);
struct sa { short fam; unsigned short port; int addr; char zero[8]; };
int main() {
  struct sa s;
  s.port = 1;
  s.zero[7] = 1;
  memset(&s, 0, sizeof(s));
  if (s.port != 0 || s.zero[7] != 0) reach_error();
  return 0;
}
