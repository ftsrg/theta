// memcpy between malloc'd structs with an inline struct member copies the member's bytes
// along with the rest, and the copy does not alias its source.
extern void abort(void);
void reach_error() { abort(); }
void *malloc(unsigned long);
void *memcpy(void *, const void *, unsigned long);

struct in { char x; };
struct out { char a; struct in in; };

int main(void) {
  struct out *s = malloc(sizeof(struct out)), *d = malloc(sizeof(struct out));
  if (!s || !d) return 0;
  s->a = 1;
  s->in.x = 2;
  memcpy(d, s, sizeof(struct out));
  s->in.x = 0;
  if (d->a != 1 || d->in.x != 2) reach_error();
  return 0;
}
