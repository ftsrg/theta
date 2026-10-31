// Brace elision in a local array of structs under the bytes model: `{5, 6, {7}}` fills the first
// element's leaves, then braces the second.
extern void abort(void);
void reach_error() { abort(); }

struct pair { int x, y; };

int main(void) {
  struct pair lp[2] = {5, 6, {7}};
  if (lp[0].y != 6 || lp[1].x != 7 || lp[1].y != 0) reach_error();
  return 0;
}
