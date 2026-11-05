// A labeled block is a scope.
typedef unsigned long int pthread_t; extern int pthread_create(pthread_t *t, const void *a, void *(*s)(void *), void *arg); extern int pthread_join(pthread_t t, void **r); extern void pthread_exit(void *r); extern int __VERIFIER_nondet_int(void);
int main(void){ int *p = 0; lab: { int x = 1; p = &x; } return *p; }
