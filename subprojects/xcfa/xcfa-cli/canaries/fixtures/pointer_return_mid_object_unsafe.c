// A returned mid-object pointer still reads the right cell.
typedef unsigned long int pthread_t; extern int pthread_create(pthread_t *t, const void *a, void *(*s)(void *), void *arg); extern int pthread_join(pthread_t t, void **r); extern void pthread_exit(void *r); extern int __VERIFIER_nondet_int(void);
extern void reach_error(void); extern void abort(void); int keys[4];  int *h(void){ return &keys[1]; } int main(void){ keys[1] = 7; int *q = h(); if (*q == 7) reach_error(); return 0; }
