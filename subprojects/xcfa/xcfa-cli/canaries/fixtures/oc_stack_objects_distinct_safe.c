// Two threads running one function, and two calls in one thread, each have their own local.
extern void reach_error(void); typedef unsigned long int pthread_t; extern int pthread_create(pthread_t *t, const void *a, void *(*s)(void *), void *arg); extern int pthread_join(pthread_t t, void **r);
void set(int *p, int v) { *p = v; }
int get(int v) { int x; set(&x, v); return x; }
int shared;
void *w(void *arg) {
  int x = 0;
  set(&x, 1);
  int y = get(2);
  int z = get(3);
  if (x != 1 || y != 2 || z != 3) reach_error();
  return 0;
}
int main(void) {
  pthread_t t1, t2;
  pthread_create(&t1, 0, w, 0);
  pthread_create(&t2, 0, w, 0);
  pthread_join(t1, 0);
  pthread_join(t2, 0);
  return 0;
}
