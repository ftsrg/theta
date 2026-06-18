// Concurrent violation: the writer thread writes x=1 before main reads x,
// so the branch on x in main is taken and reach_error is called.
// Preprocessed equivalent of the sv-witnesses concurrent-unreach.c example.

typedef unsigned long int pthread_t;
union pthread_attr_t { char __size[56]; long int __align; };
typedef union pthread_attr_t pthread_attr_t;
extern int pthread_create(pthread_t *__newthread, const pthread_attr_t *__attr, void *(*__start_routine)(void *), void *__arg);
extern int pthread_join(pthread_t __th, void **__thread_return);

void reach_error() {}

int x = 0;

void *writer(void *arg) {
    x = 1;
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
