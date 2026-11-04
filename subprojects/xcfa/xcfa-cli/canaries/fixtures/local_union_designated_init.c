// A local union's brace initializer is written to the cells its members are read from, by the
// code a global union's goes through. It was stored as one cell of the union's own type, which no
// member read looks at, so `lu.i` came back unconstrained.
extern void abort(void);
void reach_error() { abort(); }

union U {
  int i;
  char c[4];
};

int main(void) {
  union U lu = {.i = 6};
  if (lu.i != 6 || lu.c[1] != 0) reach_error();
  return 0;
}
