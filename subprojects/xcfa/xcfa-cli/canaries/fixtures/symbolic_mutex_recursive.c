#include <pthread.h>
extern unsigned long __VERIFIER_nondet_ulong(void);
extern void abort(void);
void reach_error(void) { abort(); }

pthread_mutex_t a, b;
pthread_mutex_t *selected;

void *other_thread(void *arg) {
  if (pthread_mutex_trylock(selected) == 0) reach_error();
  return 0;
}

int main(void) {
  pthread_mutexattr_t attr;
  pthread_mutexattr_init(&attr);
  pthread_mutexattr_settype(&attr, PTHREAD_MUTEX_RECURSIVE);
  pthread_mutex_init(&a, &attr);
  pthread_mutex_init(&b, &attr);
  pthread_mutexattr_destroy(&attr);
  unsigned long address = __VERIFIER_nondet_ulong();
  if (address != (unsigned long)&a && address != (unsigned long)&b) return 0;
  selected = (pthread_mutex_t *)address;
  pthread_mutex_lock(selected);
  pthread_mutex_lock(selected);
  pthread_mutex_unlock(selected);
  pthread_t thread;
  pthread_create(&thread, 0, other_thread, 0);
  pthread_join(thread, 0);
  pthread_mutex_unlock(selected);
  if (pthread_mutex_trylock(selected) != 0) reach_error();
  pthread_mutex_unlock(selected);
  return 0;
}
