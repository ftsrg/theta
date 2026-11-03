// A global array whose elements contain an inline struct member: element `i` spans the
// element's full cell count, nested member included, so neighbouring elements never share a
// cell and a write to `arr[i]` leaves `arr[i-1]` untouched.
extern void abort(void);
void reach_error() { abort(); }
extern int __VERIFIER_nondet_int(void);

struct in { int x; int y; };
struct out { int a; struct in in; int b; };
struct out arr[3];

int main(void) {
  int i = __VERIFIER_nondet_int();
  if (i < 0 || i > 2) return 0;
  arr[i].in.y = 4;
  arr[i].b = 5;
  arr[i].a = 6;
  if (arr[i].in.y != 4) reach_error();
  if (i > 0 && arr[i - 1].b == 5 && arr[i - 1].in.y == 4) reach_error();
  return 0;
}
