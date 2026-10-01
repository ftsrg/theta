// The atomic block becomes one edge that first writes `idx`, then writes `a[*pidx]`: the index read
// sees the block's own write, so the thread writes a[1] and races with main. Evaluating the address
// before the block would read idx == 0 and miss the race.
typedef unsigned long int pthread_t;
typedef union {
  char __size[36];
  long int __align;
} pthread_attr_t;
extern int pthread_create(pthread_t *__newthread, const pthread_attr_t *__attr,
                          void *(*__start_routine)(void *), void *__arg);
extern int pthread_join(pthread_t __th, void **__thread_return);
extern void __VERIFIER_atomic_begin(void);
extern void __VERIFIER_atomic_end(void);

int a[2];
int idx = 0;
int *pidx = &idx;

void *thr(void *arg) {
  __VERIFIER_atomic_begin();
  *pidx = 1;
  a[*pidx] = 2;
  __VERIFIER_atomic_end();
  return 0;
}

int main(void) {
  pthread_t id;
  pthread_create(&id, 0, thr, 0);
  a[1] = 1;
  pthread_join(id, 0);
  return 0;
}
