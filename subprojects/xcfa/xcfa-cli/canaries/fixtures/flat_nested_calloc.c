// calloc zeroes every cell of a struct with an inline struct member, the member's included.
extern void abort(void);
void reach_error() { abort(); }
void *calloc(unsigned long, unsigned long);

struct in { int x; int y; };
struct out { int a; struct in in; int b; };

int main(void) {
  struct out *o = calloc(1, sizeof(struct out));
  if (!o) return 0;
  if (o->a != 0 || o->in.x != 0 || o->in.y != 0 || o->b != 0) reach_error();
  return 0;
}
