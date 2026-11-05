// Re-entering a block through a backward goto gives a live local.
typedef unsigned long int pthread_t; extern int pthread_create(pthread_t *t, const void *a, void *(*s)(void *), void *arg); extern int pthread_join(pthread_t t, void **r); extern void pthread_exit(void *r); extern int __VERIFIER_nondet_int(void);
int main(void){ int y = 0; int *q = &y; again: if (*q < 2) { int x = 1; int *p = &x; *q += *p; goto again; } return *q - 2; }
