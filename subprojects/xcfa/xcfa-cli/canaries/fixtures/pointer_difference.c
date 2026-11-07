// A pointer difference is a ptrdiff_t counted in elements: it is divided by the element's
// cells (or bytes under the bytes model) and is as wide as a pointer.
extern void abort(void);
void reach_error() { abort(); }

struct S {
  int a;
  long b;
  char c;
};

int main() {
  struct S s[5];
  struct S *p = &s[4];
  struct S *q = s + 1;
  int a[4];
  int *r = &a[3];
  if (p - q != 3 || q - p != -3 || p - q - 1 != 2 || p + 1 - q != 4) reach_error();
  if (r - a != 3) reach_error();
  if (sizeof(p - q) != sizeof(long)) reach_error();
  return 0;
}
