// Elements of an array of unions -- a local one, a global one, and one that is a struct member --
// are distinct objects: a write to one element is not seen through another array's element.
extern void abort(void);
void reach_error() { abort(); }

union u { int i; char c[4]; };
struct holder { int k; union u arr[2]; };
union u ga[2];

int main(void) {
  union u la[2];
  struct holder h;
  la[1].i = 5;
  ga[1].i = 6;
  h.arr[1].i = 7;
  h.k = 1;
  if (la[1].i != 5 || ga[1].i != 6 || h.arr[1].i != 7 || h.k != 1) reach_error();
  return 0;
}
