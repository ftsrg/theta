// Inlining module_init into main leaves main ahead of thread1, whose mutex flag main initializes.
typedef unsigned long int pthread_t;
typedef union {
  char __size[40];
  long int __align;
} pthread_mutex_t;
extern int pthread_create(pthread_t *thread, const void *attr, void *(*start)(void *), void *arg);
extern int pthread_join(pthread_t thread, void **ret);
extern int pthread_mutex_init(pthread_mutex_t *mutex, const void *attr);
extern int pthread_mutex_lock(pthread_mutex_t *mutex);
extern int pthread_mutex_unlock(pthread_mutex_t *mutex);
extern int __VERIFIER_nondet_int();
extern void reach_error();

pthread_t t1;
pthread_mutex_t mutex;
int pdev;

void *thread1(void *arg) {
  pthread_mutex_lock(&mutex);
  pdev = 6;
  if (pdev != 6) reach_error();
  pthread_mutex_unlock(&mutex);
  return 0;
}

int module_init() {
  pthread_mutex_init(&mutex, 0);
  pdev = 1;
  if (__VERIFIER_nondet_int()) {
    pthread_create(&t1, 0, thread1, 0);
    return 0;
  }
  return -1;
}

void module_exit() {
  void *status;
  pthread_join(t1, &status);
  pdev = 5;
}

int main(void) {
  if (module_init() != 0) return 0;
  module_exit();
  return 0;
}
