// A second frontend build in one JVM (here the multi -> flat fallback, forced by storing a
// mid-object pointer) reused the first build's static struct registry: `ELEM` resolved to the
// stale type, and the element copy `t->e[0] = t->e[i]` was refused as an unhandled left-hand side.
extern void abort(void);
void reach_error() { abort(); }

struct Elem { unsigned char a; unsigned char b; };
typedef struct Elem ELEM;
struct Table { unsigned char n; ELEM e[3]; };
typedef struct Table *PTABLE;
struct Holder { int *p; };

int arr[2];
struct Holder h;

void copy(PTABLE t, unsigned long i) { t->e[0] = t->e[i]; }

int main(void) {
  struct Table t;
  h.p = &arr[1];
  t.e[1].a = 5;
  t.e[1].b = 7;
  copy(&t, 1);
  if (t.e[0].a != 5 || t.e[0].b != 7) reach_error();
  return 0;
}
