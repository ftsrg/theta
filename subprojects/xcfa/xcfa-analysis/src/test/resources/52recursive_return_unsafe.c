// sum is recursive, so it is not inlined: its result is passed back on the call stack.
extern void abort(void);
void reach_error() { abort(); }

int sum(int n) {
  if (n <= 0) return 0;
  return n + sum(n - 1);
}

int main(void) {
  if (sum(2) == 3) reach_error();
  return 0;
}
