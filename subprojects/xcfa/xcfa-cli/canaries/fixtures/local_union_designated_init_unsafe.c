// The planted-bug twin of local_union_designated_init.c: the initialized value is really read.
extern void abort(void);
void reach_error() { abort(); }

union U {
  int i;
  char c[4];
};

int main(void) {
  union U lu = {.i = 6};
  if (lu.c[0] == 6) reach_error();
  return 0;
}
