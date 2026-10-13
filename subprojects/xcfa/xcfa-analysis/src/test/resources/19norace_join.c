// The accesses are ordered by thread creation and join: no race.
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t *thread, const void *attr, void *(*start)(void *), void *arg);
extern int pthread_join(pthread_t thread, void **ret);

int x;

void *t(void *arg) {
  x = 1;
  return 0;
}

int main(void) {
  pthread_t th;
  x = 3;
  pthread_create(&th, 0, t, 0);
  pthread_join(th, 0);
  x = 2;
  return 0;
}
