#include <pthread.h>
extern unsigned long __VERIFIER_nondet_ulong(void);
extern void abort(void);
void reach_error(void) { abort(); }

pthread_mutex_t a, b;

int main(void) {
  pthread_mutex_init(&a, 0);
  pthread_mutex_init(&b, 0);
  unsigned long address = __VERIFIER_nondet_ulong();
  if (address != (unsigned long)&a && address != (unsigned long)&b) return 0;
  pthread_mutex_t *p = (pthread_mutex_t *)address;
  pthread_mutex_t *other = p == &a ? &b : &a;
  pthread_mutex_lock(p);
  if (pthread_mutex_trylock(p) == 0) reach_error();
  if (pthread_mutex_trylock(other) != 0) reach_error();
  pthread_mutex_unlock(other);
  pthread_mutex_unlock(p);
  if (pthread_mutex_trylock(p) != 0) reach_error();
  pthread_mutex_unlock(p);
  return 0;
}
