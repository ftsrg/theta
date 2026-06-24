// Concurrent violation guarded by a mutex. The writer thread sets shared=1
// under the lock; main then reads shared==1 under the lock and calls reach_error.
// The mutex object `themutex` is a pthread_mutex_t: Theta models it internally as an
// integer, but it is non-scalar in C, so it must never appear in a witness c_expression.

typedef unsigned long int pthread_t;
union pthread_attr_t { char __size[56]; long int __align; };
typedef union pthread_attr_t pthread_attr_t;
typedef union { char __size[40]; long int __align; } pthread_mutex_t;

extern int pthread_create(pthread_t *__newthread, const pthread_attr_t *__attr, void *(*__start_routine)(void *), void *__arg);
extern int pthread_join(pthread_t __th, void **__thread_return);
extern int pthread_mutex_lock(pthread_mutex_t *__mutex);
extern int pthread_mutex_unlock(pthread_mutex_t *__mutex);

void reach_error() {}

int shared = 0;
pthread_mutex_t themutex;

void *writer(void *arg) {
    pthread_mutex_lock(&themutex);
    shared = 1;
    pthread_mutex_unlock(&themutex);
    return ((void *)0);
}

int main(void) {
    pthread_t t;
    pthread_create(&t, ((void *)0), writer, ((void *)0));
    pthread_mutex_lock(&themutex);
    if (shared == 1) {
        reach_error();
    }
    pthread_mutex_unlock(&themutex);
    pthread_join(t, ((void *)0));
    return 0;
}
