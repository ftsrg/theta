// Reading a struct of longs byte by byte: the multi model has one cell per member, so the program
// has to be rebuilt under the bytes model, where byte 2 is a byte of the zeroed member `a`.
extern void abort(void);
void reach_error() { abort(); }
extern void *memset(void *, int, unsigned long);

struct S { long a; long b; };

int main() {
  struct S s;
  memset(&s, 0, sizeof s);
  const unsigned char *p = (const unsigned char *)&s;
  if (p[2]) reach_error();
  return 0;
}
