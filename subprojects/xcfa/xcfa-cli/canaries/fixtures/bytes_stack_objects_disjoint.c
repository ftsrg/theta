// Stack objects under the bytes model are allocated by their byte size: a struct whose members
// span more bytes than it has members does not run into the next local.
extern void abort(void);
void reach_error() { abort(); }

struct s { char c; short h; int k; };

int main(void) {
  struct s v;
  int t[2];
  v.k = 1;
  t[0] = 2;
  if (v.k != 1) reach_error();
  return 0;
}
