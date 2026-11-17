// The shared value is only written under a guard bounding what is written: the value analysis rules
// out the error without the solver.
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t *thread, void *attr, void *(*start_routine)(void *), void *arg);
extern int pthread_join(pthread_t thread, void **retval);
extern void reach_error(void);
int src = -1;
int head;
void *run(void *arg) {
  int n = __atomic_load_n(&src, 5);
  if (n >= 0) {
    int m = n;
    int old = __atomic_load_n(&head, 5);
    __atomic_compare_exchange_n(&head, &old, m, 0, 5, 5);
  }
  return 0;
}
int main() {
  pthread_t t;
  pthread_create(&t, 0, run, 0);
  __atomic_store_n(&src, 2, 5);
  pthread_join(t, 0);
  if (__atomic_load_n(&head, 5) < 0) reach_error();
  return 0;
}
