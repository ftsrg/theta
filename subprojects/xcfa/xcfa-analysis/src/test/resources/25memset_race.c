// The thread clears the array with memset while main writes one of its elements: a race.
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
  a[1] = 1;
  pthread_join(th, 0);
  return 0;
}
