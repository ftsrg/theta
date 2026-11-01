// `pair_t *p` with `typedef int pair_t[2]` is a pointer to the whole array, so `(*p)[i]` indexes
// the array it points to; it must not be read as an array of two pointers.
extern void abort(void);
void reach_error(void) { abort(); }

typedef int pair_t[2];
typedef pair_t *pair_p;
pair_t g;

int main(void) {
  pair_t *p = &g;
  pair_p q = &g;
  (*p)[1] = 7;
  g[0] = 3;
  if ((*q)[1] != 7) reach_error();
  if ((*p)[0] != 3) reach_error();
  return 0;
}
