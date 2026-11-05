// A direct call of `alloca` is sized in bytes like `__builtin_alloca`.
extern void *alloca(unsigned long);
int main(void) {
  int *a = alloca(4 * sizeof(int));
  a[3] = 3;
  a[4] = 4;
  return 0;
}
