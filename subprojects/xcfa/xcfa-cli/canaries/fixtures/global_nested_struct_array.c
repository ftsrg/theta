// A global array of structs lays each element inline, so element i's nested struct field is cell
// i*k + offset, holding that subobject's base. Every such cell must be written: left unconstrained,
// `ti->cell` could alias PushOpen. Element 1's scalar cells must be zero as well.
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
struct ThreadInfo threads[4];
int PushOpen[2];

int main() {
  struct ThreadInfo *ti = &threads[1];
  ti->cell.pdata = 5;
  if (PushOpen[1] != 0) reach_error();
  if (threads[2].cell.pdata != 0 || threads[1].id != 0) reach_error();
  return 0;
}
