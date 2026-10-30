// The planted-bug twin of brace_elision_struct_array.c: the elided element really is filled.
extern void abort(void);
void reach_error() { abort(); }

struct P {
  int x, y;
};

int main(void) {
  struct P lp[2] = {5, 6, {7}};
  if (lp[0].y == 6 && lp[1].x == 7) reach_error();
  return 0;
}
