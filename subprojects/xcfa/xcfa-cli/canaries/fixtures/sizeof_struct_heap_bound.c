// A heap block of padded structs holds exactly as many elements as sizeof says: the block's bound is
// its byte count divided by the same size, so the element after the last one is out of bounds.
extern void *malloc(unsigned int);
extern void free(void *);

struct P { char c; int a[2]; };

int main() {
  struct P *p = malloc(3 * sizeof(struct P));
  if (!p) return 0;
  p[2].a[1] = 1;
  p[3].c = 1;
  free(p);
  return 0;
}
