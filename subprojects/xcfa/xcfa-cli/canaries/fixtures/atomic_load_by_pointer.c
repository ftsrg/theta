// The generic `__atomic_load(p, &ret, order)` returns the value through its second argument; it
// used to be lowered like `__atomic_load_n`, leaving `ret` unwritten.
extern void abort(void);
void reach_error(){ abort(); }

long x;

int main(void) {
  long v = 0;
  __atomic_store_n(&x, 3, 5);
  __atomic_load(&x, &v, 5);
  if (v != 3) reach_error();
  return 0;
}
