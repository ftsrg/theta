// A union member of an inline-laid-out struct keeps an object of its own (its members overlap
// at offset 0); a struct inside that union must not spill into the parent's following member.
extern void abort(void);
void reach_error() { abort(); }

struct in { int x; int y; };
struct out {
  int tag;
  union {
    int raw;
    struct in in;
  } u;
  int after;
};

int main(void) {
  struct out o;
  o.after = 4;
  o.u.in.x = 1;
  o.u.in.y = 2;
  if (o.after != 4 || o.u.in.y != 2) reach_error();
  return 0;
}
