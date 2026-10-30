// typeof over a literal or an arithmetic result, which has no declaration to take its type
// from -- e.g. the kernel's max() macro declares `typeof(32) _max1 = (32);`.
extern void abort(void);
void reach_error() { abort(); }

int main() {
  unsigned long x = 3;
  typeof(32) a = 32;
  typeof(a * 2) b = 64;
  typeof(x + 1) c = 0;
  c = c - 1;                                    /* wraps: typeof kept it unsigned long */
  if (sizeof(a) != sizeof(int) || sizeof(b) != sizeof(int)) reach_error();
  if (sizeof(c) != sizeof(unsigned long) || c < 0) reach_error();
  if (a + b != 96) reach_error();
  return 0;
}
