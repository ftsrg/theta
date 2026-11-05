// A racy pointer is checked before use: the read must still see the other thread's write.
extern void reach_error(void); typedef unsigned long int pthread_t; extern int pthread_create(pthread_t *t, const void *a, void *(*s)(void *), void *arg); extern int pthread_join(pthread_t t, void **r);
int a, b;
int *p = 0;
void *w(void *arg) { b = 1; p = &b; return 0; }
int main(void) {
  pthread_t t;
  pthread_create(&t, 0, w, 0);
  int *q = p;
  if (q != 0 && *q == 1) reach_error();
  pthread_join(t, 0);
  return 0;
}
