// The error is behind a guard that rules out the only value reaching it: the value analysis
// discharges it without the solver.
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t *thread, void *attr, void *(*start_routine)(void *), void *arg);
extern int pthread_join(pthread_t thread, void **retval);
extern void reach_error(void);
int src = -1;
void *run(void *arg) {
  int n = __atomic_load_n(&src, 5);
  if (n >= 0) {
    if (n < 1) reach_error();
  }
  return 0;
}
int main() {
  pthread_t t;
  pthread_create(&t, 0, run, 0);
  __atomic_store_n(&src, 2, 5);
  pthread_join(t, 0);
  return 0;
}
