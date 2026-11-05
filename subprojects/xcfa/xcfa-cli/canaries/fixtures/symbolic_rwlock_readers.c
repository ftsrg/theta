#include <pthread.h>
#include <stdatomic.h>
extern unsigned long __VERIFIER_nondet_ulong(void);
extern void abort(void);
void reach_error(void) { abort(); }

pthread_rwlock_t a = PTHREAD_RWLOCK_INITIALIZER;
pthread_rwlock_t b = PTHREAD_RWLOCK_INITIALIZER;
pthread_rwlock_t *selected;
_Atomic int writer_entered;

void *writer(void *arg) {
  pthread_rwlock_wrlock(selected);
  atomic_store(&writer_entered, 1);
  pthread_rwlock_unlock(selected);
  return 0;
}

int main(void) {
  unsigned long address = __VERIFIER_nondet_ulong();
  if (address != (unsigned long)&a && address != (unsigned long)&b) return 0;
  selected = (pthread_rwlock_t *)address;
  pthread_rwlock_rdlock(selected);
  pthread_rwlock_rdlock(selected);
  pthread_t thread;
  pthread_create(&thread, 0, writer, 0);
  pthread_rwlock_unlock(selected);
  if (atomic_load(&writer_entered) != 0) reach_error();
  pthread_rwlock_unlock(selected);
  pthread_join(thread, 0);
  if (atomic_load(&writer_entered) != 1) reach_error();
  return 0;
}
