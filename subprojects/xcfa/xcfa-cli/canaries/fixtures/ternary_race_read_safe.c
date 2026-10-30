// `a` is read only when `published` is set, after the write; the `?:` must not read it otherwise.
#include <pthread.h>
#include <stdatomic.h>

atomic_int published;
int a;

void *writer(void *arg) {
  a = 42;
  atomic_store(&published, 1);
  return 0;
}

int main() {
  pthread_t t;
  pthread_create(&t, 0, writer, 0);
  int r = atomic_load(&published) ? a : 0;
  (void)r;
  pthread_join(t, 0);
  return 0;
}
