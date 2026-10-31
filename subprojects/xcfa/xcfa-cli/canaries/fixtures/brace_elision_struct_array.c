// Brace elision (C17 6.7.9p20) in arrays of structs, local and global: a scalar where an element
// is expected fills that element's leaves in order, and a later braced entry starts the next
// element. Only the first leaf of the first element used to be filled. Designators in a 2-D global
// array likewise land on the element they name.
extern void abort(void);
void reach_error() { abort(); }

struct P {
  int x, y;
};
struct Q {
  int a[2];
  int b;
};

struct Q gq[2] = {1, 2, 3, {4}};
int gd[2][3] = {[1] = {[2] = 5}, [0] = {[1] = 4}};

int main(void) {
  struct P lp[2] = {5, 6, {7}};
  struct Q lq[2] = {1, 2, 3, {4}};
  if (lp[0].y != 6 || lp[1].x != 7 || lp[1].y != 0) reach_error();
  if (lq[0].a[1] != 2 || lq[0].b != 3 || lq[1].a[0] != 4 || lq[1].b != 0) reach_error();
  if (gq[0].a[1] != 2 || gq[0].b != 3 || gq[1].a[0] != 4 || gq[1].a[1] != 0) reach_error();
  if (gd[1][2] != 5 || gd[0][1] != 4 || gd[1][0] != 0) reach_error();
  return 0;
}
