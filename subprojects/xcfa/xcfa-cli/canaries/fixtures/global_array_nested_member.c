// The elements of a global struct array are stored inline, so a nested member of one is
// initialized in place and gets its own storage there (#602).
extern void abort(void);
void reach_error() { abort(); }

struct In {
  int x;
};
struct E {
  int tag;
  struct In a;
  struct In b;
};

struct E arr[3] = {{7, {1}, {2}}, [2] = {.b = {5}}};

int main() {
  if (arr[0].tag != 7 || arr[0].a.x != 1 || arr[0].b.x != 2) reach_error();
  if (arr[1].a.x != 0 || arr[1].b.x != 0 || arr[2].b.x != 5) reach_error();
  struct In *p = &arr[1].b;
  arr[0].b.x = 3;
  p->x = 4;
  if (arr[0].b.x != 3 || arr[1].b.x != 4 || arr[2].b.x != 5) reach_error();
  return 0;
}
