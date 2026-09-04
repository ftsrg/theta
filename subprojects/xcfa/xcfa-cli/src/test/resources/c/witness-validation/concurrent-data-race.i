// Concurrent data race: two threads write to x with no synchronization.
// Property: G ! data-race
// Preprocessed equivalent of the sv-witnesses concurrent-data-race.c example.

typedef unsigned long int pthread_t;
union pthread_attr_t { char __size[56]; long int __align; };
typedef union pthread_attr_t pthread_attr_t;
extern int pthread_create(pthread_t *__newthread, const pthread_attr_t *__attr, void *(*__start_routine)(void *), void *__arg);
extern int pthread_join(pthread_t __th, void **__thread_return);

int x = 0;

void *t1_func(void *arg) {
    x = 1;
    return ((void *)0);
}

void *t2_func(void *arg) {
    x = 2;
    return ((void *)0);
}

int main(void) {
    pthread_t ta, tb;
    pthread_create(&ta, ((void *)0), t1_func, ((void *)0));
    pthread_create(&tb, ((void *)0), t2_func, ((void *)0));
    pthread_join(ta, ((void *)0));
    pthread_join(tb, ((void *)0));
    return 0;
}
