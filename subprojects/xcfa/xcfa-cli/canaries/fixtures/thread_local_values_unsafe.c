extern void reach_error(void);
typedef unsigned long int pthread_t;
union pthread_attr_t { char __size[36]; long int __align; };
typedef union pthread_attr_t pthread_attr_t;
extern int pthread_create (pthread_t *__restrict __newthread, const pthread_attr_t *__restrict __attr, void *(*__start_routine) (void *), void *__restrict __arg) __attribute__ ((__nothrow__));
extern int pthread_join (pthread_t __th, void **__thread_return);
static __thread int slot;
int *shared;
void *t(void *a) { shared = &slot; if (slot == 5) reach_error(); return 0; }
void *u(void *a) { int *p = shared; if (p != 0) *p = 5; return 0; }
int main(void) { pthread_t a, b; pthread_create(&a, 0, t, 0); pthread_create(&b, 0, u, 0); pthread_join(a, 0); pthread_join(b, 0); return 0; }
