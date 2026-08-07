// `__builtin_prefetch` is a cache hint with no semantic effect, but it has no declaration to
// resolve, so it killed the frontend as "No such variable or macro: __builtin_prefetch" -- it
// shows up in preprocessed kernel sources, where list walks prefetch the next node.
//
// Dropping the hint is only half of it: the *operands* are still ordinary expressions and C
// evaluates them. The `i++` below pins that -- if the arguments were discarded unevaluated,
// `i` would still be 0 and the last check would fire. It also covers the optional second and
// third arguments (rw, locality), which is the form the kernel sources actually use.
extern void abort(void);
void reach_error(){ abort(); }

int main() {
  int a[4] = {1, 2, 3, 4};
  int *p = a;
  int i = 0;

  __builtin_prefetch(p);
  __builtin_prefetch(&a[2], 0, 3);
  __builtin_prefetch((void const *)&a[i++]);

  /* the hint changed nothing it pointed at */
  if (a[0] != 1) reach_error();
  if (a[2] != 3) reach_error();

  /* but the argument's side effect did happen */
  if (i != 1) reach_error();

  return 0;
}
