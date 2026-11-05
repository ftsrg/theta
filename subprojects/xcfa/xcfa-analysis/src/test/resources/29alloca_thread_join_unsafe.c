// Both threads localize the allocator counter in their first unit; the entry thread's copy-in
// must not read it before its initialization, or every execution becomes infeasible.
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t *thread, const void *attr, void *(*start)(void *), void *arg);
extern int pthread_join(pthread_t thread, void **ret);
extern void reach_error(void);

void *t(void *arg) {
  int buf[8];
  return 0;
}

int main(void) {
  pthread_t th;
  int x;
  pthread_create(&th, 0, t, &x);
  pthread_join(th, 0);
  reach_error();
  return 0;
}
