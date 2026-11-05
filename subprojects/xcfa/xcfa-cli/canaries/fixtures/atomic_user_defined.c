// A program's own function named like a C11 atomic operation was replaced by the builtin
// model. A defined function must be called; a declared-only one still gets the model.
extern void abort(void);
void reach_error() { abort(); }

int atomic_load(int *p) { return *p + 1; }
long atomic_fetch_add(long *p, int v);

int main() {
  int x = 1;
  if (atomic_load(&x) != 2) reach_error();
  long y = 5;
  if (atomic_fetch_add(&y, 3) != 5 || y != 8) reach_error();
  return 0;
}
