// `__builtin_alloca(n)` is sized in bytes: four ints are four cells, and index 4 overruns them.
int main(void) {
  int* a = __builtin_alloca(4 * sizeof(int));
  a[3] = 3;
  a[4] = 4;
  return 0;
}
