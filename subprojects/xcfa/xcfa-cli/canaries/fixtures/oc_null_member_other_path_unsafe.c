// The pointer may be NULL or an object: the path through the object still reaches the error.
extern void reach_error(void);
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t* t, const void* a, void* (*s)(void*), void* arg);
extern int pthread_join(pthread_t t, void** r);
struct node {
  int a;
  int b;
};
struct node n = {0, 7};
struct node* p = 0;
void* w(void* arg) {
  p = &n;
  return 0;
}
int main(void) {
  pthread_t t;
  pthread_create(&t, 0, w, 0);
  pthread_join(t, 0);
  if (p->b == 7)
    reach_error();
  return 0;
}
