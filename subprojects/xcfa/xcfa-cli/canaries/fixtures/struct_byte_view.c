// A struct viewed through a character pointer by a direct cast and by memcpy into a byte buffer.
extern void abort(void);
void reach_error() { abort(); }
typedef unsigned long size_t;
void *memcpy(void *dst, const void *src, size_t n);

struct S {
  int a;
  int b;
};

int main() {
  struct S s = {1, 2};
  const unsigned char *p = (const unsigned char *)&s;
  if (p[4] != 2) reach_error();
  unsigned char buf[8];
  memcpy(buf, &s, sizeof s);
  if (buf[4] != 2 || buf[5] != 0) reach_error();
  return 0;
}
