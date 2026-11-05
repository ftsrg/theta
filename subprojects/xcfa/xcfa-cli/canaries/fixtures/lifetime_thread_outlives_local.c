// A thread can outlive the local it was given.
typedef unsigned long int pthread_t; extern int pthread_create(pthread_t *t, const void *a, void *(*s)(void *), void *arg); extern int pthread_join(pthread_t t, void **r); extern void pthread_exit(void *r); extern int __VERIFIER_nondet_int(void);
void *rd(void *a){ return (void *)(long)*(int *)a; } void f(pthread_t *t){ int x = 0; pthread_create(t,0,rd,&x); } int main(void){ pthread_t t; f(&t); pthread_join(t,0); return 0; }
