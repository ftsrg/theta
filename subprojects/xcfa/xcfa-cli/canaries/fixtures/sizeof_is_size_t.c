// `sizeof` is a size_t (unsigned long): `sizeof(int) * 2^30` is 2^32 on LP64, not a 32-bit
// product that wraps to 0 under bitvector arithmetic.
extern void abort(void);
void reach_error(void) { abort(); }
int main(void) {
  unsigned long s = sizeof(int) * 1073741824;
  if (s == 0) reach_error();
  if (sizeof(int) - 5 < 0) reach_error();
  return 0;
}
