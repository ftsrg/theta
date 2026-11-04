// An initializer of a global struct array whose elements hold a nested struct or array field
// (a cell holding that subobject's base) must land in the inline cells accesses read, with the
// omitted elements and members zero.
extern void abort(void);
void reach_error() { abort(); }

struct Cell {
  struct Cell *pnext;
  int pdata;
};
struct ThreadInfo {
  unsigned int id;
  int op;
  struct Cell cell;
};
struct WithArr {
  int x;
  int arr[2];
};

struct ThreadInfo t[3] = {{1, 2, {0, 3}}, [2] = {4, 5, {0, 6}}};
struct WithArr w[2] = {{1, {2, 3}}};

int main() {
  if (t[0].cell.pdata != 3 || t[2].cell.pdata != 6 || t[1].id != 0) reach_error();
  if (w[0].arr[1] != 3 || w[1].x != 0) reach_error();
  return 0;
}
