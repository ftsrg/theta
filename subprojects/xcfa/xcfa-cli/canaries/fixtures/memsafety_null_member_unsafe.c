// A member of NULL is an invalid dereference, and no object's address.
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t* t, const void* a, void* (*s)(void*), void* arg);
extern int pthread_join(pthread_t t, void** r);
extern int __VERIFIER_nondet_int(void);
struct node {
  int a;
  int b;
};
struct node n;
struct node* p;
void* w(void* arg) {
  return 0;
}
int main(void) {
  pthread_t t;
  pthread_create(&t, 0, w, 0);
  pthread_join(t, 0);
  p->b = 1;
  return 0;
}
