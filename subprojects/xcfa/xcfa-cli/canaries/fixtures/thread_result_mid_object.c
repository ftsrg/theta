// A joined mid-object thread result is a valid pointer.
typedef unsigned long int pthread_t; extern int pthread_create(pthread_t *t, const void *a, void *(*s)(void *), void *arg); extern int pthread_join(pthread_t t, void **r); extern void pthread_exit(void *r); extern int __VERIFIER_nondet_int(void);
int keys[4];  void *wk(void *a){ return &keys[1]; } int main(void){ void *r = 0; pthread_t t; keys[1] = 7; pthread_create(&t,0,wk,0); pthread_join(t,&r); return *(int *)r - 7; }
