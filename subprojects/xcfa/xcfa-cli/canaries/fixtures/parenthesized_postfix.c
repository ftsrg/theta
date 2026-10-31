// `(a++)` is `a++`: its value is read before the increment. As an initializer the increment used
// to be dropped, and in a condition or as a `&&` operand it ran before the read.
extern void abort(void);
void reach_error(){ abort(); }

int main(void) {
  int a = 0;
  int v = (a++);
  if (v != 0) reach_error();
  if (a != 1) reach_error();
  if ((a++) != 1) reach_error();
  if (a != 2) reach_error();
  int w = (a++, a);
  if (w != 3) reach_error();
  int b = 0;
  v = a && (b++);
  if (b != 1) reach_error();
  if (v != 0) reach_error();
  return 0;
}
