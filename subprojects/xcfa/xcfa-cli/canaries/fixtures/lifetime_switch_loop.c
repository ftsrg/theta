// Leaving a case block does not release the next entry's local.
typedef unsigned long int pthread_t; extern int pthread_create(pthread_t *t, const void *a, void *(*s)(void *), void *arg); extern int pthread_join(pthread_t t, void **r); extern void pthread_exit(void *r); extern int __VERIFIER_nondet_int(void);
int main(void){ int r = 0; for (int i = 0; i < 2; i++) { switch (i) { case 0: { int x = 1; int *p = &x; r += *p; break; } case 1: { int x = 2; int *p = &x; r += *p; continue; } } } return r - 3; }
