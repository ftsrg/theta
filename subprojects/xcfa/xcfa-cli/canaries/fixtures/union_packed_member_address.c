// `&` of a union member stored as bits of the union's word: the word used to be taken as the
// pointer (a cast crash, or a silently wrong model when the widths match). It is refused.
extern void abort(void);
void reach_error() { abort(); }

struct T { unsigned short head; unsigned short tail; };
union Lock { unsigned int ht; struct T t; };
struct L { union Lock u; };

int is_locked(struct L *l) {
  struct T tmp;
  tmp = *((struct T volatile *)(&l->u.t));
  return tmp.tail != tmp.head;
}

int main() {
  struct L l;
  l.u.ht = 0u;
  if (is_locked(&l)) reach_error();
  return 0;
}
