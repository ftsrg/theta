// The mutex object is a multi-cell memory partition written cell by cell at initialization: a
// from-read constraint that ignores cells makes every read of it infeasible, hiding the violation.
typedef unsigned long int pthread_t;
typedef union {
  char __size[40];
  long int __align;
} pthread_mutex_t;
extern int pthread_create(pthread_t *thread, const void *attr, void *(*start)(void *), void *arg);
extern int pthread_join(pthread_t thread, void **ret);
extern int pthread_mutex_lock(pthread_mutex_t *mutex);
extern int pthread_mutex_unlock(pthread_mutex_t *mutex);
extern void reach_error(void);
extern void abort(void);

pthread_mutex_t mutex;
int data = 0;

void *t1(void *arg) {
  pthread_mutex_lock(&mutex);
  data++;
  pthread_mutex_unlock(&mutex);
  return 0;
}

void *t2(void *arg) {
  if (data >= 1) {
    reach_error();
    abort();
  }
  return 0;
}

int main(void) {
  pthread_t th1, th2;
  pthread_create(&th1, 0, t1, 0);
  pthread_create(&th2, 0, t2, 0);
  pthread_join(th1, 0);
  pthread_join(th2, 0);
  return 0;
}
