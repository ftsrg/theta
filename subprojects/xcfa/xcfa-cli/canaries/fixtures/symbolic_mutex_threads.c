#include <pthread.h>
extern unsigned long __VERIFIER_nondet_ulong(void);
extern void abort(void);
void reach_error(void) { abort(); }

pthread_mutex_t a, b;
int counter;

void *worker(void *arg) {
  pthread_mutex_t *p = arg;
  pthread_mutex_lock(p);
  int old = counter;
  counter = old + 1;
  pthread_mutex_unlock(p);
  return 0;
}

int main(void) {
  pthread_mutex_init(&a, 0);
  pthread_mutex_init(&b, 0);
  unsigned long address = __VERIFIER_nondet_ulong();
  if (address != (unsigned long)&a && address != (unsigned long)&b) return 0;
  pthread_t first, second;
  pthread_create(&first, 0, worker, (void *)address);
  pthread_create(&second, 0, worker, (void *)address);
  pthread_join(first, 0);
  pthread_join(second, 0);
  if (counter != 2) reach_error();
  return 0;
}
