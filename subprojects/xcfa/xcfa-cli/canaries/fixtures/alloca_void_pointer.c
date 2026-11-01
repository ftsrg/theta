// An explicit alloca returns `void *`, whose pointee has no size; it must not crash the pass.
extern void abort(void);
void reach_error() { abort(); }
extern void *alloca(unsigned long);

int main() {
  char *c = (char *)alloca(4);
  c[0] = 1;
  if (c[0] != 1) reach_error();
  return 0;
}
