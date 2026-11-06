// A dereference guarded by `?:` is not reached when malloc fails, so that path is not blocked.
extern void abort(void);
void reach_error() { abort(); }
void *malloc(unsigned long);

int main(void) {
  int *p = malloc(sizeof(int));
  int x = p ? *p : 1;
  if (!p && x == 1) reach_error();
  return 0;
}
