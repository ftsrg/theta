// Concurrent violation in which the same thread-creating call is taken twice,
// but the witness registers a logical thread only on one of the visits. Both
// spawned threads run the same code, yet only the registered one is the thread
// the witness reasons about (its write is ordered before main's read), so the
// logical-thread-id guard must single it out.

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
    for (int i = 0; i < 2; i++) {
        pthread_create(&t, ((void *)0), writer, ((void *)0));
    }
    if (x == 1) {
        reach_error();
    }
    return 0;
}
