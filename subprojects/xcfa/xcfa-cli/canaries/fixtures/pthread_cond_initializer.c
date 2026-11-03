// PTHREAD_COND_INITIALIZER resolves, and pthread_cond_destroy is a no-op.
#include <pthread.h>
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "pthread_cond_initializer.c", 4, "reach_error"); }
pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;
pthread_cond_t c = PTHREAD_COND_INITIALIZER;
int ready = 0;
void *thr(void *a) { pthread_mutex_lock(&m); ready = 1; pthread_cond_signal(&c); pthread_mutex_unlock(&m); return 0; }
int main() { pthread_t t; pthread_create(&t, 0, thr, 0); pthread_mutex_lock(&m); while (!ready) pthread_cond_wait(&c, &m); pthread_mutex_unlock(&m); pthread_join(t, 0); pthread_cond_destroy(&c); if (!ready) reach_error(); return 0; }
