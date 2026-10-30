// The elements of a 2-D array of unions are distinct objects. Only the elements of a 1-D array
// were given one; a row was offset by the union's byte size while its elements stayed one cell
// each, so writes through one element were read back through another.
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
  if (l2[1][1].i != 3) reach_error();
  return 0;
}
