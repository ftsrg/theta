// A local whose address is handed to another thread is written by it.
extern void reach_error(void); typedef unsigned long int pthread_t; extern int pthread_create(pthread_t *t, const void *a, void *(*s)(void *), void *arg); extern int pthread_join(pthread_t t, void **r);
void *w(void *arg) { *(int *)arg = 1; return 0; }
int main(void) {
  int x = 0;
  pthread_t t;
  pthread_create(&t, 0, w, &x);
  pthread_join(t, 0);
  if (x == 1) reach_error();
  return 0;
}
