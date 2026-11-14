// The written cell depends on a compare-and-swap whose operands together take more values than the
// value analysis enumerates: only the values it can choose are written.
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t *thread, void *attr, void *(*start_routine)(void *), void *arg);
extern int pthread_join(pthread_t thread, void **retval);
extern void reach_error(void);
int idx;
int cell[16];
void *run(void *arg) {
  int old = __atomic_load_n(&idx, 5);
  __atomic_compare_exchange_n(&idx, &old, 12, 0, 5, 5);
  cell[__atomic_load_n(&idx, 5)] = 1;
  return 0;
}
int main() {
  pthread_t t;
  pthread_create(&t, 0, run, 0);
  __atomic_store_n(&idx, 1, 5);
  __atomic_store_n(&idx, 2, 5);
  __atomic_store_n(&idx, 3, 5);
  __atomic_store_n(&idx, 4, 5);
  __atomic_store_n(&idx, 5, 5);
  __atomic_store_n(&idx, 6, 5);
  __atomic_store_n(&idx, 7, 5);
  __atomic_store_n(&idx, 8, 5);
  __atomic_store_n(&idx, 9, 5);
  pthread_join(t, 0);
  if (cell[10] || cell[11] || cell[13]) reach_error();
  return 0;
}
