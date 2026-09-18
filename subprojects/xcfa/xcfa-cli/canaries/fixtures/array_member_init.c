// The other half of the same layout question: an array *member* of a struct is its own
// object (its base lives in the parent's cell), while an array's *elements* -- even struct
// elements -- live inline in the array's own cells. The initializer has to follow each.
extern void abort(void);
void reach_error() { abort(); }

struct Inner {
  int x, y;
};
struct WithArr {
  int a[3];
  int z;
};

int main() {
  struct WithArr w = {{5, 6}, 7}; // a[2] is not mentioned, so it is zero
  struct Inner arr[2] = {{1, 2}, {3, 4}};
  int m[2][3] = {{1, 2, 3}, {4, 5, 6}};
  if (w.a[0] != 5 || w.a[1] != 6 || w.a[2] != 0 || w.z != 7) reach_error();
  if (arr[0].x != 1 || arr[0].y != 2 || arr[1].x != 3 || arr[1].y != 4) reach_error();
  if (m[0][0] != 1 || m[0][2] != 3 || m[1][0] != 4 || m[1][2] != 6) reach_error();
  return 0;
}
