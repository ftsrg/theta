// The thread argument is an int-typed 0 while the parameter is a (64-bit) pointer.
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t *thread, void *attr, void *(*start_routine)(void *), void *arg);
extern int pthread_join(pthread_t thread, void **retval);

int g;

void *thread(void *arg) {
  g = 1;
  return 0;
}

int main() {
  pthread_t id;
  pthread_create(&id, 0, thread, 0);
  g = 2;
  pthread_join(id, 0);
  return 0;
}
