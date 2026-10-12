// Concurrent violation with a nondeterministic write in the spawned thread.
// The writer thread reads a nondet value into x; the witness pins it to 1,
// guarded by the writer's logical thread id, and orders the write before
// main's read, so reach_error() becomes reachable.

typedef unsigned long int pthread_t;
union pthread_attr_t { char __size[56]; long int __align; };
typedef union pthread_attr_t pthread_attr_t;
extern int pthread_create(pthread_t *__newthread, const pthread_attr_t *__attr, void *(*__start_routine)(void *), void *__arg);
extern int pthread_join(pthread_t __th, void **__thread_return);
extern int __VERIFIER_nondet_int(void);
void reach_error() {}

int x = 0;

void *writer(void *arg) {
    x = __VERIFIER_nondet_int();
    return ((void *)0);
}

int main(void) {
    pthread_t t;
    pthread_create(&t, ((void *)0), writer, ((void *)0));
    if (x == 1) {
        reach_error();
    }
    pthread_join(t, ((void *)0));
    return 0;
}
