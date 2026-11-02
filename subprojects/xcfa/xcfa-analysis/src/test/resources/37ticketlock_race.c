// The counter is incremented without taking the ticket lock: a race.
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t *thread, void *attr, void *(*start_routine)(void *), void *arg);
extern int pthread_join(pthread_t thread, void **retval);
typedef struct { unsigned _v; } vatomic32_t;
typedef struct { vatomic32_t next; vatomic32_t owner; } ticketlock_t;
ticketlock_t lock;
int x;
static inline unsigned get_add(vatomic32_t *a, unsigned v) { return __atomic_fetch_add(&a->_v, v, 5); }
static inline unsigned get_inc(vatomic32_t *a) { return get_add(a, 1U); }
static inline unsigned load(vatomic32_t *a) { return __atomic_load_n(&a->_v, 5); }
void acquire(ticketlock_t *l) {
  unsigned t = get_inc(&l->next);
  while (load(&l->owner) != t) {}
}
void release(ticketlock_t *l) { get_inc(&l->owner); }
void *run(void *arg) {
  get_inc(&lock.next);
  x++;
  release(&lock);
  return 0;
}
int main() {
  pthread_t t1, t2;
  pthread_create(&t1, 0, run, 0);
  pthread_create(&t2, 0, run, 0);
  pthread_join(t1, 0);
  pthread_join(t2, 0);
  return 0;
}
