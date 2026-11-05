// Reading a member through NULL crashes: the error after it is unreachable.
extern void reach_error(void); typedef unsigned long int pthread_t; extern int pthread_create(pthread_t *t, const void *a, void *(*s)(void *), void *arg); extern int pthread_join(pthread_t t, void **r);
struct node { int a; int b; };
struct node n;
struct node *p = 0;
void *w(void *arg) { return 0; }
int main(void) {
  pthread_t t;
  pthread_create(&t, 0, w, 0);
  int v = p->b;
  if (v == 7) reach_error();
  pthread_join(t, 0);
  return v;
}
