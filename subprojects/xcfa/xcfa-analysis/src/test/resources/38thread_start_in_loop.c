// The copies of the pthread_create in the unrolled loop are equal labels, but must start distinct
// threads.
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t *thread, const void *attr, void *(*start)(void *), void *arg);
extern void reach_error();

int x;

void *t(void *arg) {
  x++;
  if (x == 2) reach_error();
  return 0;
}

int main(void) {
  pthread_t th;
  for (int i = 0; i < 2; i++) {
    pthread_create(&th, 0, t, 0);
  }
  return 0;
}
