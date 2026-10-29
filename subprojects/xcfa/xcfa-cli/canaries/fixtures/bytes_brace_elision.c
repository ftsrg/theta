// Brace elision and designators under the bytes model: a scalar where an aggregate is expected
// fills that aggregate's leaves in order, and a designator moves to the named element.
extern void abort(void);
void reach_error() { abort(); }

struct pair { int x, y; };
struct pair gp[2] = {1, 2, 3, 4};
int gd[5] = {[3] = 7, 8};

int main(void) {
  struct pair lp[2] = {5, 6, {7}};
  if (gp[1].x != 3 || gp[1].y != 4 || gd[3] != 7 || gd[4] != 8 || gd[0] != 0) reach_error();
  if (lp[0].y != 6 || lp[1].x != 7 || lp[1].y != 0) reach_error();
  return 0;
}
