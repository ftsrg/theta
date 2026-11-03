// A comma after `?:`'s false branch ends the conditional (C11 6.5.15): `x = c ? 1 : 2, y = 5` is
// `(x = c ? 1 : 2), (y = 5)`. It used to parse as `x = c ? 1 : (2, y = 5)`, so `y = 5` ran only
// when `c` was false and this safe program was reported unsafe.
extern void abort(void);
void reach_error() { abort(); }

int main() {
  int c = 1;
  int x, y = 0;
  x = c ? 1 : 2, y = 5;
  if (x != 1 || y != 5) reach_error();
  return 0;
}
