// A struct and an int reach a character view through `void *`. The cell models read cell i, not
// byte i, so the program must be built under the byte-addressed model.
extern void abort(void);
void reach_error() { abort(); }
typedef unsigned long size_t;
void *memset(void *s, int c, size_t n);

struct node {
  struct node *next;
  struct node *prev;
};

static int is_zeroed(const void *buf, size_t n) {
  const unsigned char *b = (const unsigned char *)buf;
  for (size_t i = 0; i < n; ++i)
    if (b[i]) return 0;
  return 1;
}

int main() {
  struct node node;
  memset(&node, 0, sizeof(node));
  if (!is_zeroed(&node, sizeof(node))) reach_error();
  unsigned int x = 0x01020304u;
  void *v = &x;
  unsigned char *c = v;
  if (c[0] != 4 || c[3] != 1) reach_error();
  return 0;
}
