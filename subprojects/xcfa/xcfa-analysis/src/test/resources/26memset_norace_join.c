// The memset is ordered before main's write by the join: no race.
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t *thread, const void *attr, void *(*start)(void *), void *arg);
extern int pthread_join(pthread_t thread, void **ret);
extern void *memset(void *s, int c, unsigned long n);

int a[4];

void *t(void *arg) {
  memset(a, 0, sizeof(a));
  return 0;
}

int main(void) {
  pthread_t th;
  pthread_create(&th, 0, t, 0);
  pthread_join(th, 0);
  a[1] = 1;
  return 0;
}
