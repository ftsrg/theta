// A local 2-D array of unions with a brace-elided initializer: each scalar initializes the first
// member of the next element, an object of its own, and the elements left out are zero.
extern void abort(void);
void reach_error() { abort(); }

union U {
  int i;
  char c[4];
};

int main(void) {
  union U e[2][2] = {1, 2, 3};
  if (e[0][1].i != 2 || e[1][0].i != 3 || e[1][1].i != 0) reach_error();
  return 0;
}
