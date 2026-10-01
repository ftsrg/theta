// Global arrays whose struct elements are inline but not one scalar per cell: packed bitfields,
// and a 2-D array of structs with a nested struct field. Their initializers must land in the
// cells accesses read, and the rest must be zero.
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
struct Bits {
  unsigned a : 4, b : 4;
  int c;
};

struct Bits bs[2] = {{1, 2, 3}};
struct ThreadInfo grid[2][2] = {{{7, 0, {0, 8}}}};

int main() {
  if (bs[0].b != 2 || bs[1].a != 0) reach_error();
  if (grid[0][0].cell.pdata != 8 || grid[1][1].cell.pdata != 0) reach_error();
  return 0;
}
