// A statement expression runs its statements in order, each with its own side effects, also as an
// initializer or an assigned value: the call used to run before `p = &c`, and `i++` was dropped.
extern void abort(void);
void reach_error(){ abort(); }

int c;
int get(int *p) { return *p; }

int main(void) {
  c = 1;
  int v = ({ int *p = &c; get(p); });
  if (v != 1) reach_error();
  int w;
  w = ({ int i = 0; i++; i; });
  if (w != 1) reach_error();
  return 0;
}
