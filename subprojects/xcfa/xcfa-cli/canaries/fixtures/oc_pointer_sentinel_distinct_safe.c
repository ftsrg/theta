// An integer sentinel is no object's address, even of the first object in memory.
extern void reach_error(void); typedef unsigned long int pthread_t; extern int pthread_create(pthread_t *t, const void *a, void *(*s)(void *), void *arg); extern int pthread_join(pthread_t t, void **r);
int first;
int *p = &first;
void *w(void *arg) { return 0; }
int main(void) {
  pthread_t t;
  pthread_create(&t, 0, w, 0);
  if (p == (int *)1) reach_error();
  pthread_join(t, 0);
  return 0;
}
