// `a` is read while `published` is still clear, so the read races with the write.
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
  int r = atomic_load(&published) ? 0 : a;
  (void)r;
  pthread_join(t, 0);
  return 0;
}
