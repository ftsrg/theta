// An uninitialized local was not given a fresh value when its declaration ran again. Inlining
// splices every call of `func` onto the same variables, so the second call read `x == 1` left by
// the first and `x == 2` became unreachable: `Safe` for a program whose second call may fail.
extern void abort(void);
void reach_error() { abort(); }

void func(int a) {
  int x;
  if (a == 1 && x == 2) reach_error();
  x = 1;
}

int main() {
  func(0);
  func(1);
  return 0;
}
