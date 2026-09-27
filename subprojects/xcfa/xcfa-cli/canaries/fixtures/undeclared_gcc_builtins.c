// GCC builtins arrive with no declaration: the `__builtin_` spellings of memset/memcpy/memmove,
// which MemoryFunctionsPass models like the plain ones, and the legacy `__sync_*` atomics, which
// are the `__atomic_*` ones under sequential consistency.
extern void abort(void);
void reach_error() { abort(); }
extern void *malloc(unsigned long);

int main(void) {
  char *p = malloc(4);
  if (!p) return 0;
  __builtin_memset(p, 0, 4);
  if (p[0] != 0 || p[3] != 0) reach_error();
  char src[4] = {1, 2, 3, 4};
  __builtin_memcpy(p, src, 4);
  if (p[0] != 1 || p[3] != 4) reach_error();
  src[3] = 8;
  __builtin_memmove(p, src, 4);
  if (p[3] != 8) reach_error();

  int c = 5;
  if (__sync_fetch_and_add(&c, 2) != 5 || c != 7) reach_error();
  if (__sync_sub_and_fetch(&c, 3) != 4) reach_error();
  if (__sync_lock_test_and_set(&c, 9) != 4 || c != 9) reach_error();
  __sync_synchronize();
  return 0;
}
