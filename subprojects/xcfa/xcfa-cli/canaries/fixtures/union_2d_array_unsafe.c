// The planted-bug twin of union_2d_array.c: the element keeps what was written to it.
extern void abort(void);
void reach_error() { abort(); }

union U {
  int i;
  char c[4];
};

int main(void) {
  union U l2[2][2];
  l2[1][1].i = 3;
  l2[0][1].i = 2;
  if (l2[1][1].i == 3) reach_error();
  return 0;
}
